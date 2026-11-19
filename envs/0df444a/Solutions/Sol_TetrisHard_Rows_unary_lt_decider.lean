-- Prove2me | solution 1 for TetrisHard.Rows.unary_lt_decider
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T01:20:45.448359+00:00
-- url     : https://prove2.me/submissions/46dc17c0-334f-4bbb-9f98-902d7543ee42

import Mathlib
import Definitions.Def_TetrisHard_Rows_ThreePartition

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace UnaryLtM

open CookPvsNP

abbrev Γ : Type := Option (Option (Bool ⊕ Bool))
abbrev Cell : Type := Option Γ

abbrev X : Γ := none
abbrev Tl : Γ := some (some (Sum.inl true))
abbrev Tr : Γ := some (some (Sum.inr true))
abbrev ans (b : Bool) : Cell := some (some (some (Sum.inr b)))

inductive St
  | s0 | s1 | s2 | fT | ret | bk | acc | rej
  deriving DecidableEq

instance : Fintype St :=
  ⟨{St.s0, St.s1, St.s2, St.fT, St.ret, St.bk, St.acc, St.rej}, fun x => by cases x <;> simp⟩

def trans : St → Cell → St × Cell × Move
  | .s0, none => (.bk, ans false, .left)
  | .s0, some none => (.s0, some none, .right)
  | .s0, some (some (some (Sum.inl true))) => (.s1, some none, .right)
  | .s0, some (some (some (Sum.inr true))) => (.fT, some (some (some (Sum.inr true))), .right)
  | .s0, some c => (.s2, some c, .right)
  | .s1, none => (.bk, ans false, .left)
  | .s1, some (some (some (Sum.inr true))) => (.ret, some none, .left)
  | .s1, some c => (.s1, some c, .right)
  | .s2, none => (.bk, ans false, .left)
  | .s2, some (some (some (Sum.inr true))) => (.fT, some (some (some (Sum.inr true))), .right)
  | .s2, some c => (.s2, some c, .right)
  | .fT, none => (.bk, ans true, .left)
  | .fT, some c => (.fT, some c, .right)
  | .ret, none => (.s0, none, .right)
  | .ret, some c => (.ret, some c, .left)
  | .bk, c => (.acc, c, .right)
  | .acc, c => (.acc, c, .right)
  | .rej, c => (.rej, c, .right)

def M : TM Γ where
  Q := St
  q₀ := .s0
  qaccept := .acc
  qreject := .rej
  accept_ne_reject := by decide
  δ := trans

def mk (q : St) (L w : List Cell) : Cfg Γ M.Q :=
  { state := q, left := L, head := w.headD none, right := w.tail }

def strip (l : List Cell) : List Cell :=
  (l.reverse.dropWhile Option.isNone).reverse

theorem output_mk (q : St) (L w : List Cell) : M.output (mk q L w) = strip w := by
  cases w with
  | nil => simp [TM.output, mk, strip]
  | cons c w => simp [TM.output, mk, strip]

theorem not_halting {q : St} (h1 : q ≠ .acc) (h2 : q ≠ .rej) (L w : List Cell) :
    ¬ M.IsHalting (mk q L w) := by
  intro h
  rcases h with h | h
  · exact h1 h
  · exact h2 h

theorem step_right {q q' : St} {c' : Cell} (L w : List Cell) (h1 : q ≠ .acc)
    (h2 : q ≠ .rej) (hδ : trans q (w.headD none) = (q', c', Move.right)) :
    M.step (mk q L w) = mk q' (c' :: L) w.tail := by
  unfold TM.step
  rw [if_neg (not_halting h1 h2 L w)]
  have h : M.δ (mk q L w).state (mk q L w).head = (q', c', Move.right) := hδ
  simp only [h]
  rfl

theorem step_left {q q' : St} {c' : Cell} (a : Cell) (L w : List Cell)
    (h1 : q ≠ .acc) (h2 : q ≠ .rej) (hδ : trans q (w.headD none) = (q', c', Move.left)) :
    M.step (mk q (a :: L) w) = mk q' L (a :: c' :: w.tail) := by
  unfold TM.step
  rw [if_neg (not_halting h1 h2 (a :: L) w)]
  have h : M.δ (mk q (a :: L) w).state (mk q (a :: L) w).head = (q', c', Move.left) := hδ
  simp only [h]
  rfl

theorem step_left_nil {q q' : St} {c' : Cell} (w : List Cell)
    (h1 : q ≠ .acc) (h2 : q ≠ .rej) (hδ : trans q (w.headD none) = (q', c', Move.left)) :
    M.step (mk q [] w) = mk q' [] (none :: c' :: w.tail) := by
  unfold TM.step
  rw [if_neg (not_halting h1 h2 [] w)]
  have h : M.δ (mk q [] w).state (mk q [] w).head = (q', c', Move.left) := hδ
  simp only [h]
  rfl

theorem run_succ (n : ℕ) (c : Cfg Γ M.Q) : M.run (n + 1) c = M.run n (M.step c) := by
  simp [TM.run, Function.iterate_succ_apply]

theorem run_add (a b : ℕ) (c : Cfg Γ M.Q) : M.run (a + b) c = M.run a (M.run b c) :=
  Function.iterate_add_apply _ _ _ _

theorem run_halting (n : ℕ) (c : Cfg Γ M.Q) (h : M.IsHalting c) : M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : M.step c = c := by
      unfold TM.step
      rw [if_pos h]
    rw [run_succ, hs, ih]

theorem run_mono {n N : ℕ} (c : Cfg Γ M.Q) (h : M.IsHalting (M.run n c)) (hN : n ≤ N) :
    M.run N c = M.run n c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_comm, run_add, run_halting _ _ h]

def Good (c : Cfg Γ M.Q) (n : ℕ) (out : List Cell) : Prop :=
  ∃ m, m ≤ n ∧ M.IsHalting (M.run m c) ∧ M.output (M.run m c) = out

theorem Good.of_step {c c' : Cfg Γ M.Q} (h : M.step c = c')
    {n : ℕ} {out : List Cell} (hg : Good c' n out) : Good c (n + 1) out := by
  obtain ⟨m, hm, h1, h2⟩ := hg
  refine ⟨m + 1, by omega, ?_, ?_⟩
  · rw [run_succ, h]; exact h1
  · rw [run_succ, h]; exact h2

theorem Good.of_run {c c' : Cfg Γ M.Q} {k : ℕ} (h : M.run k c = c')
    {n : ℕ} {out : List Cell} (hg : Good c' n out) : Good c (k + n) out := by
  obtain ⟨m, hm, h1, h2⟩ := hg
  refine ⟨m + k, by omega, ?_, ?_⟩
  · rw [run_add, h]; exact h1
  · rw [run_add, h]; exact h2

theorem Good.mono {c : Cfg Γ M.Q} {n n' : ℕ} {out : List Cell}
    (hg : Good c n out) (h : n ≤ n') : Good c n' out := by
  obtain ⟨m, hm, h1, h2⟩ := hg
  exact ⟨m, by omega, h1, h2⟩

/-! ### Abstract semantics -/

def hasTr : List Γ → Bool
  | [] => false
  | c :: t => if c = Tr then true else hasTr t

theorem hasTr_iff : ∀ t : List Γ, hasTr t = true ↔ Tr ∈ t
  | [] => by simp [hasTr]
  | c :: t => by
    by_cases hc : c = Tr
    · subst hc; simp [hasTr]
    · simp [hasTr, hc, hasTr_iff t, Ne.symm hc]

def s1scan : List Γ → Option (List Γ)
  | [] => none
  | some (some (Sum.inr true)) :: t => some (none :: t)
  | c :: t => (s1scan t).map (c :: ·)

def s0scan : List Γ → Bool ⊕ List Γ
  | [] => .inl false
  | none :: t => Sum.map id (none :: ·) (s0scan t)
  | some (some (Sum.inl true)) :: t =>
      match s1scan t with
      | none => .inl false
      | some t' => .inr (none :: t')
  | c :: t => .inl (hasTr (c :: t))

def A : ℕ → List Γ → Bool
  | 0, _ => false
  | n + 1, t =>
      match s0scan t with
      | .inl b => b
      | .inr t' => A n t'

def cnt : List Γ → ℕ
  | [] => 0
  | c :: t => cnt t + if c = Tl then 1 else 0

theorem cnt_le (t : List Γ) : cnt t ≤ t.length := by
  induction t with
  | nil => simp [cnt]
  | cons c t ih => simp only [cnt, List.length_cons]; split <;> omega

theorem s1scan_cons {c : Γ} (hc : c ≠ Tr) (t : List Γ) :
    s1scan (c :: t) = (s1scan t).map (c :: ·) := by
  rcases c with _ | (_ | (b | b)) <;> (try cases b) <;> first | rfl | exact absurd rfl hc

theorem s1scan_Tr (t : List Γ) : s1scan (Tr :: t) = some (X :: t) := rfl

theorem s0scan_X (t : List Γ) : s0scan (X :: t) = Sum.map id (X :: ·) (s0scan t) := rfl

theorem s0scan_Tl (t : List Γ) : s0scan (Tl :: t) =
    match s1scan t with
    | none => .inl false
    | some t' => .inr (X :: t') := rfl

theorem s0scan_other {c : Γ} (h1 : c ≠ X) (h2 : c ≠ Tl) (t : List Γ) :
    s0scan (c :: t) = .inl (hasTr (c :: t)) := by
  rcases c with _ | (_ | (b | b)) <;> (try cases b) <;>
    first | rfl | exact absurd rfl h1 | exact absurd rfl h2

theorem s1scan_some : ∀ (t t' : List Γ), s1scan t = some t' →
    t'.length = t.length ∧ cnt t' = cnt t
  | [], t', h => by simp [s1scan] at h
  | c :: t, t', h => by
    by_cases hc : c = Tr
    · subst hc
      rw [s1scan_Tr] at h
      cases h
      simp [cnt]
    · rw [s1scan_cons hc] at h
      cases h2 : s1scan t with
      | none => rw [h2] at h; simp at h
      | some t'' =>
        rw [h2] at h
        simp at h
        subst h
        obtain ⟨e1, e2⟩ := s1scan_some t t'' h2
        simp [cnt, e1, e2]

theorem s0scan_inr : ∀ (t t' : List Γ), s0scan t = .inr t' →
    t'.length = t.length ∧ cnt t' < cnt t
  | [], t', h => by simp [s0scan] at h
  | c :: t, t', h => by
    by_cases hX : c = X
    · subst hX
      rw [s0scan_X] at h
      cases h2 : s0scan t with
      | inl b => rw [h2] at h; simp at h
      | inr t'' =>
        rw [h2] at h
        simp at h
        subst h
        obtain ⟨e1, e2⟩ := s0scan_inr t t'' h2
        simp [cnt, e1]
        omega
    by_cases hT : c = Tl
    · subst hT
      rw [s0scan_Tl] at h
      cases h2 : s1scan t with
      | none => rw [h2] at h; simp at h
      | some t'' =>
        rw [h2] at h
        simp at h
        subst h
        obtain ⟨e1, e2⟩ := s1scan_some t t'' h2
        simp [cnt, e1, e2]
    · rw [s0scan_other hX hT] at h
      simp at h

/-! ### Machine phases -/

theorem write_good (q : St) (b : Bool) (h1 : q ≠ .acc) (h2 : q ≠ .rej)
    (hδ : trans q none = (.bk, ans b, .left)) (K : List Cell) :
    Good (mk q K []) 2 [ans b] := by
  cases K with
  | nil =>
    have s1 : M.step (mk q [] []) = mk .bk [] (none :: ans b :: []) :=
      step_left_nil [] h1 h2 hδ
    have s2 : M.step (mk .bk [] (none :: ans b :: [])) = mk .acc [none] [ans b] :=
      step_right [] _ (by decide) (by decide) rfl
    refine ⟨2, le_rfl, ?_, ?_⟩
    · rw [run_succ, s1, run_succ, s2]; exact Or.inl rfl
    · rw [run_succ, s1, run_succ, s2]
      show M.output (mk .acc [none] [ans b]) = _
      rw [output_mk]; simp [strip]
  | cons k K =>
    have s1 : M.step (mk q (k :: K) []) = mk .bk K (k :: ans b :: []) :=
      step_left k K [] h1 h2 hδ
    have s2 : M.step (mk .bk K (k :: ans b :: [])) = mk .acc (k :: K) [ans b] :=
      step_right K _ (by decide) (by decide) rfl
    refine ⟨2, le_rfl, ?_, ?_⟩
    · rw [run_succ, s1, run_succ, s2]; exact Or.inl rfl
    · rw [run_succ, s1, run_succ, s2]
      show M.output (mk .acc (k :: K) [ans b]) = _
      rw [output_mk]; simp [strip]

theorem fT_good : ∀ (t : List Γ) (K : List Cell),
    Good (mk .fT K (t.map some)) (t.length + 2) [ans true]
  | [], K => write_good .fT true (by decide) (by decide) rfl K
  | c :: t, K => by
    have s : M.step (mk .fT K ((c :: t).map some)) = mk .fT (some c :: K) (t.map some) :=
      step_right K (some c :: t.map some) (by decide) (by decide) rfl
    have h := fT_good t (some c :: K)
    exact (Good.of_step s h).mono (by simp)

theorem trans_s2 {c : Γ} (hc : c ≠ Tr) : trans .s2 (some c) = (.s2, some c, .right) := by
  rcases c with _ | (_ | (b | b)) <;> (try cases b) <;> first | rfl | exact absurd rfl hc

theorem trans_s1 {c : Γ} (hc : c ≠ Tr) : trans .s1 (some c) = (.s1, some c, .right) := by
  rcases c with _ | (_ | (b | b)) <;> (try cases b) <;> first | rfl | exact absurd rfl hc

theorem trans_s0 {c : Γ} (h1 : c ≠ X) (h2 : c ≠ Tl) (hc : c ≠ Tr) :
    trans .s0 (some c) = (.s2, some c, .right) := by
  rcases c with _ | (_ | (b | b)) <;> (try cases b) <;>
    first | rfl | exact absurd rfl hc | exact absurd rfl h1 | exact absurd rfl h2

theorem s2_good : ∀ (t : List Γ) (K : List Cell),
    Good (mk .s2 K (t.map some)) (t.length + 2) [ans (hasTr t)]
  | [], K => by
    exact write_good .s2 false (by decide) (by decide) rfl K
  | c :: t, K => by
    by_cases hc : c = Tr
    · subst hc
      have s : M.step (mk .s2 K ((Tr :: t).map some)) = mk .fT (some Tr :: K) (t.map some) :=
        step_right K (some Tr :: t.map some) (by decide) (by decide) rfl
      have h := fT_good t (some Tr :: K)
      have e : hasTr (Tr :: t) = true := by simp [hasTr]
      rw [e]
      exact (Good.of_step s h).mono (by simp)
    · have s : M.step (mk .s2 K ((c :: t).map some)) = mk .s2 (some c :: K) (t.map some) :=
        step_right K (some c :: t.map some) (by decide) (by decide) (trans_s2 hc)
      have h := s2_good t (some c :: K)
      have e : hasTr (c :: t) = hasTr t := by
        simp [hasTr, hc]
      rw [e]
      exact (Good.of_step s h).mono (by simp)

theorem s1_none : ∀ (t : List Γ) (K : List Cell), s1scan t = none →
    Good (mk .s1 K (t.map some)) (t.length + 2) [ans false]
  | [], K, _ => write_good .s1 false (by decide) (by decide) rfl K
  | c :: t, K, h => by
    by_cases hc : c = Tr
    · subst hc; rw [s1scan_Tr] at h; cases h
    · rw [s1scan_cons hc] at h
      have h' : s1scan t = none := by
        cases h2 : s1scan t with
        | none => rfl
        | some _ => rw [h2] at h; simp at h
      have s : M.step (mk .s1 K ((c :: t).map some)) = mk .s1 (some c :: K) (t.map some) :=
        step_right K (some c :: t.map some) (by decide) (by decide) (trans_s1 hc)
      exact (Good.of_step s (s1_none t (some c :: K) h')).mono (by simp)

theorem walk (L : List Cell) : ∀ (J : List Γ) (h : Γ) (R : List Cell),
    M.run J.length (mk .ret (J.map some ++ L) (some h :: R)) =
      mk .ret L ((J.reverse ++ [h]).map some ++ R)
  | [], h, R => by simp [TM.run]
  | j :: J, h, R => by
    rw [List.length_cons, run_succ]
    have s : M.step (mk .ret ((j :: J).map some ++ L) (some h :: R)) =
        mk .ret (J.map some ++ L) (some j :: some h :: R) :=
      step_left (q := .ret) (q' := .ret) (some j) (J.map some ++ L) (some h :: R) (by decide) (by decide) rfl
    rw [s, walk L J j (some h :: R)]
    simp

theorem home0 (R : List Cell) : M.run 1 (mk .ret [] (none :: R)) = mk .s0 [none] R := by
  rw [run_succ]
  exact step_right (q := .ret) (q' := .s0) [] (none :: R) (by decide) (by decide) rfl

theorem home_end (L : List Cell) (hL : L = [] ∨ L = [none]) (g : Γ) (R : List Cell) :
    M.run 2 (mk .ret L (some g :: R)) = mk .s0 [none] (some g :: R) := by
  have s1 : M.step (mk .ret L (some g :: R)) = mk .ret [] (none :: some g :: R) := by
    rcases hL with rfl | rfl
    · exact step_left_nil (some g :: R) (by decide) (by decide) rfl
    · exact step_left none [] (some g :: R) (by decide) (by decide) rfl
  rw [run_succ, s1]
  exact home0 _

theorem home (L : List Cell) (hL : L = [] ∨ L = [none]) (J : List Γ) (h : Γ) (R : List Cell) :
    ∃ k ≤ J.length + 2, M.run k (mk .ret (J.map some ++ L) (some h :: R)) =
      mk .s0 [none] ((J.reverse ++ [h]).map some ++ R) := by
  have hw := walk L J h R
  obtain ⟨g, R', hR⟩ : ∃ g R', (J.reverse ++ [h]).map some ++ R = some g :: R' := by
    cases hr : J.reverse with
    | nil => exact ⟨h, R, by simp⟩
    | cons g0 J' => exact ⟨g0, (J' ++ [h]).map some ++ R, by simp⟩
  refine ⟨2 + J.length, by omega, ?_⟩
  rw [run_add, hw, hR, home_end L hL]

theorem s1_some (L : List Cell) (hL : L = [] ∨ L = [none]) : ∀ (t pre t' : List Γ),
    s1scan t = some t' →
    ∃ k ≤ pre.length + 2 * t.length + 3,
      M.run k (mk .s1 (pre.reverse.map some ++ L) (t.map some)) = mk .s0 [none] ((pre ++ t').map some)
  | [], pre, t', h => by simp [s1scan] at h
  | c :: t, pre, t', h => by
    by_cases hc : c = Tr
    · subst hc
      rw [s1scan_Tr] at h
      cases h
      rcases List.eq_nil_or_concat pre with rfl | ⟨pre', j, rfl⟩
      · have s1 : M.step (mk .s1 (([] : List Γ).reverse.map some ++ L) ((Tr :: t).map some)) =
            mk .ret [] (none :: some X :: t.map some) := by
          rcases hL with rfl | rfl
          · exact step_left_nil (some Tr :: t.map some) (by decide) (by decide) rfl
          · exact step_left none [] (some Tr :: t.map some) (by decide) (by decide) rfl
        refine ⟨2, by simp, ?_⟩
        rw [run_succ, s1, home0]
        simp
      · simp only [List.concat_eq_append]
        have e : (pre' ++ [j]).reverse.map some ++ L = some j :: (pre'.reverse.map some ++ L) := by
          simp
        rw [e]
        have s1 : M.step (mk .s1 (some j :: (pre'.reverse.map some ++ L)) ((Tr :: t).map some)) =
            mk .ret (pre'.reverse.map some ++ L) (some j :: some X :: t.map some) :=
          step_left (some j) _ (some Tr :: t.map some) (by decide) (by decide) rfl
        obtain ⟨k, hk, hr⟩ := home L hL pre'.reverse j (some X :: t.map some)
        refine ⟨k + 1, by simp only [List.length_reverse] at hk; simp; omega, ?_⟩
        rw [run_succ, s1, hr]
        simp
    · rw [s1scan_cons hc] at h
      cases h2 : s1scan t with
      | none => rw [h2] at h; simp at h
      | some t'' =>
        rw [h2] at h
        simp at h
        subst h
        have s : M.step (mk .s1 (pre.reverse.map some ++ L) ((c :: t).map some)) =
            mk .s1 ((pre ++ [c]).reverse.map some ++ L) (t.map some) := by
          have := step_right (pre.reverse.map some ++ L) (some c :: t.map some) (by decide)
            (by decide) (trans_s1 hc)
          simpa using this
        obtain ⟨k, hk, hr⟩ := s1_some L hL t (pre ++ [c]) t'' h2
        refine ⟨k + 1, by simp at hk ⊢; omega, ?_⟩
        rw [run_succ, s, hr]
        simp

theorem s0_good (L : List Cell) (hL : L = [] ∨ L = [none]) : ∀ (t pre : List Γ),
    (∀ b, s0scan t = .inl b →
      Good (mk .s0 (pre.reverse.map some ++ L) (t.map some))
        (2 * pre.length + 3 * t.length + 4) [ans b]) ∧
    (∀ t', s0scan t = .inr t' → ∃ k ≤ 2 * pre.length + 3 * t.length + 4,
      M.run k (mk .s0 (pre.reverse.map some ++ L) (t.map some)) = mk .s0 [none] ((pre ++ t').map some))
  | [], pre => by
    refine ⟨fun b h => ?_, fun t' h => by simp [s0scan] at h⟩
    simp [s0scan] at h
    subst h
    exact (write_good .s0 false (by decide) (by decide) rfl _).mono (by simp)
  | c :: t, pre => by
    by_cases hX : c = X
    · subst hX
      have s : M.step (mk .s0 (pre.reverse.map some ++ L) ((X :: t).map some)) =
          mk .s0 ((pre ++ [X]).reverse.map some ++ L) (t.map some) := by
        have := step_right (pre.reverse.map some ++ L) (some X :: t.map some) (by decide)
          (by decide) (rfl : trans .s0 (some X) = (.s0, some X, .right))
        simpa using this
      obtain ⟨ih1, ih2⟩ := s0_good L hL t (pre ++ [X])
      rw [s0scan_X]
      constructor
      · intro b h
        cases h2 : s0scan t with
        | inr _ => rw [h2] at h; simp at h
        | inl b' =>
          rw [h2] at h; simp at h; subst h
          exact (Good.of_step s (ih1 b' h2)).mono (by simp; omega)
      · intro t' h
        cases h2 : s0scan t with
        | inl _ => rw [h2] at h; simp at h
        | inr t'' =>
          rw [h2] at h; simp at h; subst h
          obtain ⟨k, hk, hr⟩ := ih2 t'' h2
          refine ⟨k + 1, by simp at hk ⊢; omega, ?_⟩
          rw [run_succ, s, hr]
          simp
    by_cases hT : c = Tl
    · subst hT
      have s : M.step (mk .s0 (pre.reverse.map some ++ L) ((Tl :: t).map some)) =
          mk .s1 ((pre ++ [X]).reverse.map some ++ L) (t.map some) := by
        have := step_right (pre.reverse.map some ++ L) (some Tl :: t.map some) (by decide)
          (by decide) (rfl : trans .s0 (some Tl) = (.s1, some X, .right))
        simpa using this
      rw [s0scan_Tl]
      constructor
      · intro b h
        cases h2 : s1scan t with
        | some _ => rw [h2] at h; simp at h
        | none =>
          rw [h2] at h; simp at h; subst h
          exact (Good.of_step s (s1_none t _ h2)).mono (by simp; omega)
      · intro t' h
        cases h2 : s1scan t with
        | none => rw [h2] at h; simp at h
        | some t'' =>
          rw [h2] at h; simp at h; subst h
          obtain ⟨k, hk, hr⟩ := s1_some L hL t (pre ++ [X]) t'' h2
          refine ⟨k + 1, by simp at hk ⊢; omega, ?_⟩
          rw [run_succ, s, hr]
          simp
    rw [s0scan_other hX hT]
    refine ⟨fun b h => ?_, fun t' h => by simp at h⟩
    simp only [Sum.inl.injEq] at h
    subst h
    by_cases hc : c = Tr
    · subst hc
      have s : M.step (mk .s0 (pre.reverse.map some ++ L) ((Tr :: t).map some)) =
          mk .fT (some Tr :: (pre.reverse.map some ++ L)) (t.map some) :=
        step_right _ (some Tr :: t.map some) (by decide) (by decide) rfl
      have e : hasTr (Tr :: t) = true := by simp [hasTr]
      rw [e]
      exact (Good.of_step s (fT_good t _)).mono (by simp; omega)
    · have s : M.step (mk .s0 (pre.reverse.map some ++ L) ((c :: t).map some)) =
          mk .s2 (some c :: (pre.reverse.map some ++ L)) (t.map some) :=
        step_right _ (some c :: t.map some) (by decide) (by decide) (trans_s0 hX hT hc)
      have e : hasTr (c :: t) = hasTr t := by
        simp [hasTr, hc]
      rw [e]
      exact (Good.of_step s (s2_good t _)).mono (by simp; omega)

theorem main : ∀ (n : ℕ) (t : List Γ) (L : List Cell), (L = [] ∨ L = [none]) → cnt t < n →
    Good (mk .s0 L (t.map some)) (n * (3 * t.length + 4)) [ans (A n t)]
  | 0, t, L, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, t, L, hL, h => by
    obtain ⟨h1, h2⟩ := s0_good L hL t []
    cases hs : s0scan t with
    | inl b =>
      have hA : A (n + 1) t = b := by simp [A, hs]
      rw [hA]
      have := h1 b hs
      simp only [List.reverse_nil, List.map_nil, List.nil_append, List.length_nil,
        Nat.mul_zero, Nat.zero_add] at this
      exact this.mono (by nlinarith)
    | inr t' =>
      have hA : A (n + 1) t = A n t' := by simp [A, hs]
      rw [hA]
      obtain ⟨k, hk, hr⟩ := h2 t' hs
      simp only [List.reverse_nil, List.map_nil, List.nil_append, List.length_nil,
        Nat.mul_zero, Nat.zero_add] at hk hr
      obtain ⟨e1, e2⟩ := s0scan_inr t t' hs
      have ih := main n t' [none] (Or.inr rfl) (by omega)
      rw [e1] at ih
      exact (Good.of_run hr ih).mono (by nlinarith)

/-! ### Well-formed inputs -/

def word (i a v : ℕ) : List Γ :=
  List.replicate i X ++ List.replicate a Tl ++ some (some (Sum.inl false)) :: some none ::
    (List.replicate i X ++ List.replicate v Tr ++ [some (some (Sum.inr false))])

theorem s0scan_rep (i : ℕ) (t : List Γ) :
    s0scan (List.replicate i X ++ t) = Sum.map id (List.replicate i X ++ ·) (s0scan t) := by
  induction i with
  | zero => simp only [List.replicate_zero, List.nil_append]; cases s0scan t <;> rfl
  | succ i ih =>
    rw [List.replicate_succ, List.cons_append, s0scan_X, ih]
    cases s0scan t <;> rfl

theorem s1scan_app : ∀ (W t : List Γ), Tr ∉ W → s1scan (W ++ t) = (s1scan t).map (W ++ ·)
  | [], t, _ => by simp
  | c :: W, t, h => by
    have hc : c ≠ Tr := fun e => h (e ▸ List.mem_cons_self)
    have hW : Tr ∉ W := fun e => h (List.mem_cons_of_mem _ e)
    rw [List.cons_append, s1scan_cons hc, s1scan_app W t hW]
    cases s1scan t <;> rfl

theorem s1scan_nil : ∀ (W : List Γ), Tr ∉ W → s1scan W = none
  | [], _ => rfl
  | c :: W, h => by
    have hc : c ≠ Tr := fun e => h (e ▸ List.mem_cons_self)
    have hW : Tr ∉ W := fun e => h (List.mem_cons_of_mem _ e)
    rw [s1scan_cons hc, s1scan_nil W hW]
    rfl

theorem A_word : ∀ (a n i v : ℕ), a < n → A n (word i a v) = decide (a < v)
  | a, 0, i, v, h => absurd h (Nat.not_lt_zero _)
  | 0, n + 1, i, v, _ => by
    have hs : s0scan (word i 0 v) = .inl (decide (0 < v)) := by
      unfold word
      rw [List.append_assoc, s0scan_rep]
      simp only [List.replicate_zero, List.nil_append]
      rw [s0scan_other (by decide) (by decide)]
      simp only [Sum.map_inl, id_eq]
      congr 1
      rw [Bool.eq_iff_iff, hasTr_iff]
      cases v <;> simp [List.mem_replicate]
    simp [A, hs]
  | a + 1, n + 1, i, v, h => by
    cases v with
    | zero =>
      have hs : s0scan (word i (a + 1) 0) = .inl false := by
        unfold word
        rw [List.append_assoc, s0scan_rep, List.replicate_succ, List.cons_append, s0scan_Tl,
          s1scan_nil _ (by simp [List.mem_replicate])]
        rfl
      simp [A, hs]
    | succ v =>
      have hs : s0scan (word i (a + 1) (v + 1)) = .inr (word (i + 1) a v) := by
        unfold word
        rw [List.append_assoc, s0scan_rep, List.replicate_succ, List.cons_append, s0scan_Tl]
        have e : List.replicate a Tl ++ some (some (Sum.inl false)) :: some none ::
            (List.replicate i X ++ List.replicate (v + 1) Tr ++ [some (some (Sum.inr false))]) =
            (List.replicate a Tl ++ some (some (Sum.inl false)) :: some none ::
              List.replicate i X) ++ (Tr :: (List.replicate v Tr ++ [some (some (Sum.inr false))])) := by
          simp [List.replicate_succ]
        rw [e, s1scan_app _ _ (by simp [List.mem_replicate]), s1scan_Tr]
        simp [List.replicate_succ', List.replicate_succ]
      have ih := A_word a n (i + 1) v (by omega)
      simp [A, hs, ih]

end UnaryLtM

open CookPvsNP in
theorem solution :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable g ∧
      ∀ a v : ℕ, g ((TetrisHard.Rows.unaryCode [a]).map (some ∘ Sum.inl) ++
        none :: (TetrisHard.Rows.unaryCode [v]).map (some ∘ Sum.inr)) = [decide (a < v)] := by
  refine ⟨fun x => [UnaryLtM.A (x.length + 1) (x.map some)], ?_, ?_⟩
  · refine ⟨UnaryLtM.Γ, inferInstance, ⟨some, Option.some_injective _⟩,
      ⟨fun b => some (some (Sum.inr b)), fun b b' h => by simpa using h⟩, UnaryLtM.M, 14, ?_⟩
    intro x
    have hg := UnaryLtM.main (x.length + 1) (x.map some) [] (Or.inl rfl)
      (by have := UnaryLtM.cnt_le (x.map some); simp at this; omega)
    obtain ⟨m, hm, hhalt, hout⟩ := hg
    have hb : (x.length + 1) * (3 * (x.map some).length + 4) ≤ x.length ^ 14 + 14 := by
      simp only [List.length_map]
      rcases Nat.lt_or_ge x.length 2 with h | h
      · interval_cases x.length <;> norm_num
      · have h1 : x.length ^ 2 ≤ x.length ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have h2 : 4 ≤ x.length ^ 2 := by nlinarith
        have h3 : x.length ^ 14 = x.length ^ 2 * x.length ^ 12 := by ring
        nlinarith
    have hrun := UnaryLtM.run_mono _ hhalt (le_trans hm hb)
    have hinit : UnaryLtM.M.init (x.map (⟨some, Option.some_injective _⟩ :
        Option (Bool ⊕ Bool) ↪ UnaryLtM.Γ)) = UnaryLtM.mk .s0 [] ((x.map some).map some) := rfl
    constructor
    · unfold TM.HaltsWithin
      rw [hinit, hrun]
      exact hhalt
    · rw [hinit, hrun, hout]
      rfl
  · intro a v
    have e : ((TetrisHard.Rows.unaryCode [a]).map (some ∘ Sum.inl) ++
        none :: (TetrisHard.Rows.unaryCode [v]).map (some ∘ Sum.inr)).map some =
        UnaryLtM.word 0 a v := by
      simp [TetrisHard.Rows.unaryCode, UnaryLtM.word]
    simp only [List.cons.injEq, and_true]
    rw [e, UnaryLtM.A_word a _ 0 v (by simp [TetrisHard.Rows.unaryCode]; try omega)]

