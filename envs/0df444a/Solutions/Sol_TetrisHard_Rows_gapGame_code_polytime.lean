-- Prove2me | solution 1 for TetrisHard.Rows.gapGame_code_polytime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:37:03.663278+00:00
-- url     : https://prove2.me/submissions/a5dbd9b5-7216-4a55-9436-0ff5487ee499

import Definitions.Def_TetrisHard_Rows_GapReduction
import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open CookPvsNP

namespace NoBoundPf

abbrev K := Fin 16

def st (b : K → List Bool) (r : K → ℕ) : K → List Bool :=
  fun k => List.replicate (r k) true ++ b k

def Run (p : StackProg K Bool) (s t : K → List Bool) (B : ℕ) : Prop :=
  ∃ n ≤ B, p.Exec s t n

theorem Run.mono {p : StackProg K Bool} {s t : K → List Bool} {B B' : ℕ}
    (h : Run p s t B) (hB : B ≤ B') : Run p s t B' := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨n, hn.trans hB, he⟩

theorem Run.seq {p q : StackProg K Bool} {s t u : K → List Bool} {B C : ℕ}
    (h1 : Run p s t B) (h2 : Run q t u C) : Run (.seq p q) s u (B + 1 + C) := by
  obtain ⟨n, hn, he⟩ := h1; obtain ⟨m, hm, hf⟩ := h2
  exact ⟨n + 1 + m, by omega, .seq he hf⟩

theorem Run.branchT {test : (K → Option Bool) → Bool} {p q : StackProg K Bool}
    {s t : K → List Bool} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true) (h : Run p s t B) :
    Run (.branch test p q) s t (1 + B) := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨1 + n, by omega, .branchTrue ht he⟩

theorem Run.branchF {test : (K → Option Bool) → Bool} {p q : StackProg K Bool}
    {s t : K → List Bool} {B : ℕ}
    (ht : test (fun k => (s k).head?) = false) (h : Run q s t B) :
    Run (.branch test p q) s t (1 + B) := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨1 + n, by omega, .branchFalse ht he⟩

theorem Run.loopF {test : (K → Option Bool) → Bool} {p : StackProg K Bool}
    {s : K → List Bool} (ht : test (fun k => (s k).head?) = false) :
    Run (.loop test p) s s 1 := ⟨1, le_rfl, .loopFalse ht⟩

theorem Run.loopT {test : (K → Option Bool) → Bool} {p : StackProg K Bool}
    {s t u : K → List Bool} {B C : ℕ}
    (ht : test (fun k => (s k).head?) = true) (h1 : Run p s t B)
    (h2 : Run (.loop test p) t u C) : Run (.loop test p) s u (1 + B + 1 + C) := by
  obtain ⟨n, hn, he⟩ := h1; obtain ⟨m, hm, hf⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, .loopTrue ht he hf⟩

theorem Run.congr {p : StackProg K Bool} {s t t' : K → List Bool} {B : ℕ}
    (h : Run p s t B) (e : t = t') : Run p s t' B := e ▸ h

def noop : StackProg K Bool := .act (fun _ _ => .keep)

theorem run_noop (s : K → List Bool) : Run noop s s 1 := ⟨1, le_rfl, .act _ s⟩

theorem head_st (b : K → List Bool) (r : K → ℕ) (k : K) :
    (st b r k).head? = if 0 < r k then some true else (b k).head? := by
  unfold st; cases r k <;> simp [List.replicate_succ]

theorem head_st_nil {b : K → List Bool} (r : K → ℕ) {k : K} (hb : b k = []) :
    (st b r k).head? = if 0 < r k then some true else none := by
  rw [head_st, hb]; rfl

theorem run_push (b : K → List Bool) (r : K → ℕ) (k : K) :
    Run (pushProg k true) (st b r) (st b (Function.update r k (r k + 1))) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).1 true
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, List.replicate_succ]
  · simp [st, Function.update_of_ne hj]

theorem run_pushB (b : K → List Bool) (r : K → ℕ) (k : K) (a : Bool) :
    Run (pushProg k a) (st b r)
      (st (Function.update b k (a :: st b r k)) (Function.update r k 0)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).1 a
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st]
  · simp [st, Function.update_of_ne hj]

theorem run_pop (b : K → List Bool) (r : K → ℕ) (k : K) (n : ℕ) (hk : r k = n + 1) :
    Run (popProg k) (st b r) (st b (Function.update r k n)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).2.1
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, hk, List.replicate_succ]
  · simp [st, Function.update_of_ne hj]

theorem run_popB (b : K → List Bool) (r : K → ℕ) (k : K) (hk : r k = 0) :
    Run (popProg k) (st b r) (st (Function.update b k (b k).tail) r) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).2.1
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, hk]
  · simp [st, Function.update_of_ne hj]

theorem run_clear (b : K → List Bool) (r : K → ℕ) (k : K) (hb : b k = []) :
    Run (clearProg k) (st b r) (st b (Function.update r k 0)) (3 * r k + 1) := by
  have h := (stack_basic_macros k (st b r)).2.2
  rw [show (st b r k).length = r k by simp [st, hb]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, hb]
  · simp [st, Function.update_of_ne hj]

theorem run_copy (b : K → List Bool) (r : K → ℕ) (src dst scr : K)
    (hsd : src ≠ dst) (hst : src ≠ scr) (hdt : dst ≠ scr)
    (hbs : b src = []) (hbz : b scr = []) (hz : r scr = 0) :
    Run (copyProg src dst scr) (st b r)
      (st b (Function.update r dst (r src + r dst))) (6 * r src + 3) := by
  have h := stack_copy src dst scr hsd hst hdt (st b r) (by simp [st, hbz, hz])
  rw [show (st b r src).length = r src by simp [st, hbs]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  by_cases hj : j = dst
  · subst hj; simp [st, hbs]; rw [List.replicate_add, List.append_assoc]
  · simp [st, Function.update_of_ne hj]

theorem run_copyB (b : K → List Bool) (r : K → ℕ) (src dst scr : K)
    (hsd : src ≠ dst) (hst : src ≠ scr) (hdt : dst ≠ scr)
    (hrs : r src = 0) (hrd : r dst = 0) (hbz : b scr = []) (hz : r scr = 0) :
    Run (copyProg src dst scr) (st b r)
      (st (Function.update b dst (b src ++ b dst)) r) (6 * (b src).length + 3) := by
  have h := stack_copy src dst scr hsd hst hdt (st b r) (by simp [st, hbz, hz])
  rw [show (st b r src).length = (b src).length by simp [st, hrs]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  by_cases hj : j = dst
  · subst hj; simp [st, hrs, hrd]
  · simp [st, Function.update_of_ne hj]

theorem run_move (b : K → List Bool) (r : K → ℕ) (src dst : K) (hne : src ≠ dst)
    (hbs : b src = []) :
    Run (transferProg src (fun k => decide (k = dst))) (st b r)
      (st b (Function.update (Function.update r src 0) dst (r src + r dst)))
      (3 * r src + 1) := by
  have h := stack_transfer src (fun k => decide (k = dst)) (st b r)
  rw [show (st b r src).length = r src by simp [st, hbs]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  unfold transferStore
  by_cases hj : j = src
  · subst hj; simp [st, hbs, Function.update_of_ne hne]
  · by_cases hj' : j = dst
    · subst hj'; simp [st, hbs, hj]; rw [List.replicate_add, List.append_assoc]
    · simp [st, hj, hj', Function.update_of_ne hj, Function.update_of_ne hj']

theorem run_moveB (b : K → List Bool) (r : K → ℕ) (src dst : K) (hne : src ≠ dst)
    (hrs : r src = 0) (hrd : r dst = 0) :
    Run (transferProg src (fun k => decide (k = dst))) (st b r)
      (st (Function.update (Function.update b src []) dst ((b src).reverse ++ b dst)) r)
      (3 * (b src).length + 1) := by
  have h := stack_transfer src (fun k => decide (k = dst)) (st b r)
  rw [show (st b r src).length = (b src).length by simp [st, hrs]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  unfold transferStore
  by_cases hj : j = src
  · subst hj; simp [st, hrs, Function.update_of_ne hne]
  · by_cases hj' : j = dst
    · subst hj'; simp [st, hrs, hrd, hj]
    · simp [st, hj, hj', Function.update_of_ne hj, Function.update_of_ne hj']

/-- move a unary register onto a list-valued register with no unary part -/
theorem run_moveU (b : K → List Bool) (r : K → ℕ) (src dst : K) (hne : src ≠ dst)
    (hbs : b src = []) (hrd : r dst = 0) :
    Run (transferProg src (fun k => decide (k = dst))) (st b r)
      (st (Function.update b dst (List.replicate (r src) true ++ b dst))
        (Function.update r src 0)) (3 * r src + 1) := by
  have h := stack_transfer src (fun k => decide (k = dst)) (st b r)
  rw [show (st b r src).length = r src by simp [st, hbs]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  unfold transferStore
  by_cases hj : j = src
  · subst hj; simp [st, hbs, Function.update_of_ne hne]
  · by_cases hj' : j = dst
    · subst hj'; simp [st, hbs, hrd, hj]
    · simp [st, hj, hj', Function.update_of_ne hj, Function.update_of_ne hj']

theorem run_sync (b : K → List Bool) (r : K → ℕ) (i j : K) (hne : i ≠ j)
    (hbi : b i = []) (hbj : b j = []) :
    Run (syncPopProg i j) (st b r)
      (st b (Function.update (Function.update r i (r i - min (r i) (r j))) j
        (r j - min (r i) (r j)))) (3 * min (r i) (r j) + 1) := by
  have h := stack_sync_pop i j hne (st b r)
  simp only [show (st b r i).length = r i by simp [st, hbi],
    show (st b r j).length = r j by simp [st, hbj]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext k
  by_cases hk : k = j
  · subst hk; simp [st, hbj, List.drop_replicate]
  · by_cases hk' : k = i
    · subst hk'; simp [st, hbi, List.drop_replicate, Function.update_of_ne hk]
    · simp [st, Function.update_of_ne hk, Function.update_of_ne hk']

theorem run_repeat (b : K → List Bool) (r : K → ℕ) (e : Fin 4 ↪ K)
    (hb0 : b (e 0) = []) (hb2 : b (e 2) = []) (hb3 : b (e 3) = []) (hz : r (e 3) = 0) :
    Run (repeatCopyProg e) (st b r)
      (st b (Function.update (Function.update r (e 2) 0) (e 1) (r (e 2) * r (e 0) + r (e 1))))
      ((6 * r (e 0) + 7) * r (e 2) + 1) := by
  have h := stack_repeat_copy e (st b r) (by simp [st, hb3, hz])
  simp only [show (st b r (e 0)).length = r (e 0) by simp [st, hb0],
    show (st b r (e 2)).length = r (e 2) by simp [st, hb2]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  have h12 : e 1 ≠ e 2 := fun h => by simpa using e.injective h
  funext j
  by_cases hj : j = e 1
  · subst hj; simp [st, hb0]; rw [List.replicate_add, List.append_assoc]
  · by_cases hj' : j = e 2
    · subst hj'; simp [st, hb2, Function.update_of_ne hj]
    · simp [st, Function.update_of_ne hj, Function.update_of_ne hj']

/-- push `n` trues -/
def pushN (k : K) : ℕ → StackProg K Bool
  | 0 => noop
  | n + 1 => .seq (pushProg k true) (pushN k n)

theorem run_pushN (b : K → List Bool) (k : K) (n : ℕ) : ∀ r : K → ℕ,
    Run (pushN k n) (st b r) (st b (Function.update r k (r k + n))) (2 * n + 1) := by
  induction n with
  | zero => intro r; simpa [pushN] using run_noop (st b r)
  | succ n ih =>
    intro r
    have := (run_push b r k).seq (ih _)
    refine (this.congr ?_).mono (by omega)
    congr 1; funext j; by_cases hj : j = k
    · subst hj; simp; omega
    · simp [Function.update_of_ne hj]

/-- push a list (so that the list ends on top in order) -/
def pushL (k : K) : List Bool → StackProg K Bool
  | [] => noop
  | a :: l => .seq (pushL k l) (pushProg k a)

theorem run_pushL (k : K) (l : List Bool) : ∀ (b : K → List Bool) (r : K → ℕ), r k = 0 →
    Run (pushL k l) (st b r) (st (Function.update b k (l ++ b k)) r) (2 * l.length + 1) := by
  induction l with
  | nil => intro b r _; simpa [pushL] using run_noop (st b r)
  | cons a l ih =>
    intro b r hr
    have := (ih b r hr).seq (run_pushB _ r k a)
    refine (this.congr ?_).mono (by simp; omega)
    have : Function.update r k 0 = r := by simp [← hr]
    rw [this]; congr 1; funext j; by_cases hj : j = k
    · subst hj; simp [st, hr]
    · simp [Function.update_of_ne hj]

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

structure PS where
  cur : ℕ
  s : ℕ
  t : ℕ
  cnt : ℕ
  sum : ℕ
  bad : ℕ
  f1 : Bool
  f2 : Bool

def badInc (t e : ℕ) : ℕ := (if t < 4 * e then 0 else 1) + (if 2 * e < t then 0 else 1)

def pstep (p : PS) (x : Bool) : PS :=
  if x then { p with cur := p.cur + 1, sum := if p.f2 then p.sum + 1 else p.sum }
  else if p.f1 then
    (if p.f2 then { p with bad := p.bad + badInc p.t p.cur, cnt := p.cnt + 1, cur := 0 }
     else { p with t := p.cur + p.t, cur := 0, f2 := true })
  else { p with s := p.cur + p.s, cur := 0, f1 := true }

def p0 : PS := ⟨0, 0, 0, 0, 0, 0, false, false⟩

theorem fold_rep (n : ℕ) : ∀ p : PS, (List.replicate n true).foldl pstep p =
    { p with cur := p.cur + n, sum := if p.f2 then p.sum + n else p.sum } := by
  induction n with
  | zero => intro p; cases p; simp
  | succ n ih =>
    intro p
    rw [List.replicate_succ, List.foldl_cons, ih]
    cases p with
    | mk cur s t cnt sum bad f1 f2 =>
      cases f2 <;> simp [pstep] <;> omega

theorem unaryCode_cons (n : ℕ) (ns : List ℕ) :
    unaryCode (n :: ns) = List.replicate n true ++ false :: unaryCode ns := by
  simp [unaryCode]

theorem unaryCode_nil : unaryCode [] = [] := by simp [unaryCode]

theorem fold_entries (es : List ℕ) : ∀ p : PS, p.f1 = true → p.f2 = true → p.cur = 0 →
    (unaryCode es).foldl pstep p =
      { p with cnt := p.cnt + es.length, sum := p.sum + es.sum,
               bad := p.bad + (es.map (badInc p.t)).sum } := by
  induction es with
  | nil => intro p _ _ _; cases p; simp [unaryCode_nil]
  | cons e es ih =>
    intro p h1 h2 h0
    rw [unaryCode_cons, List.foldl_append, fold_rep, List.foldl_cons]
    cases p with
    | mk cur s t cnt sum bad f1 f2 =>
      simp only at h1 h2 h0
      subst h1 h2 h0
      rw [ih] <;> simp [pstep] <;> omega

theorem parse_full (a t : ℕ) (es : List ℕ) (k : ℕ) :
    (unaryCode (a :: t :: es) ++ List.replicate k true).foldl pstep p0 =
      ⟨k, a, t, es.length, es.sum + k, (es.map (badInc t)).sum, true, true⟩ := by
  have hc : (unaryCode (a :: t :: es)).foldl pstep p0 =
      ⟨0, a, t, es.length, es.sum, (es.map (badInc t)).sum, true, true⟩ := by
    rw [unaryCode_cons, List.foldl_append, fold_rep a, List.foldl_cons, unaryCode_cons,
      List.foldl_append, fold_rep t, List.foldl_cons, fold_entries]
    · simp [pstep, p0]
    all_goals simp [pstep, p0]
  rw [List.foldl_append, fold_rep k, hc]
  simp

theorem parse_short (ns : List ℕ) (k : ℕ) (h : ns.length < 2) :
    ((unaryCode ns ++ List.replicate k true).foldl pstep p0).f2 = false := by
  match ns, h with
  | [], _ => simp [unaryCode_nil, fold_rep, p0]
  | [a], _ =>
    rw [List.foldl_append, unaryCode_cons, List.foldl_append, fold_rep, List.foldl_cons,
      unaryCode_nil, List.foldl_nil, fold_rep]
    simp [pstep, p0]

theorem decomp (w : List Bool) : ∃ ns k, w = unaryCode ns ++ List.replicate k true := by
  induction w with
  | nil => exact ⟨[], 0, by simp [unaryCode_nil]⟩
  | cons x w ih =>
    obtain ⟨ns, k, rfl⟩ := ih
    cases x with
    | false => exact ⟨0 :: ns, k, by simp [unaryCode_cons]⟩
    | true =>
      cases ns with
      | nil => exact ⟨[], k + 1, by simp [unaryCode_nil, List.replicate_succ]⟩
      | cons n ns => exact ⟨(n + 1) :: ns, k, by simp [unaryCode_cons, List.replicate_succ]⟩

def PS.ok (q : PS) : Prop :=
  q.f2 = true ∧ q.cur = 0 ∧ q.bad = 0 ∧ q.cnt = 3 * q.s ∧ q.sum = q.s * q.t

theorem badInc_eq_zero (t e : ℕ) : badInc t e = 0 ↔ t < 4 * e ∧ 2 * e < t := by
  unfold badInc; split_ifs with h1 h2 h2 <;> simp_all <;> omega

theorem sum_map_eq_zero (l : List ℕ) (f : ℕ → ℕ) :
    (l.map f).sum = 0 ↔ ∀ e ∈ l, f e = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem code_eq (P : ThreePartition) :
    P.code = unaryCode (P.s :: P.target :: List.ofFn P.entry) ++ List.replicate 0 true := by
  simp [ThreePartition.code]

/-- the parse of the code of a valid instance -/
theorem parse_code (P : ThreePartition) (hP : P.Valid) :
    (P.code.foldl pstep p0).ok ∧ (P.code.foldl pstep p0).s = P.s ∧
      (P.code.foldl pstep p0).t = P.target := by
  rw [code_eq, parse_full]
  obtain ⟨hs, hi⟩ := hP
  refine ⟨⟨rfl, rfl, ?_, ?_, ?_⟩, rfl, rfl⟩
  · simp only
    rw [sum_map_eq_zero]
    intro e he
    rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact (badInc_eq_zero _ _).2 (hi i)
  · simp
  · simp [List.sum_ofFn, hs]

theorem parse_ok (w : List Bool) (h : (w.foldl pstep p0).ok) :
    ∃ P : ThreePartition, P.Valid ∧ w = P.code := by
  obtain ⟨ns, k, rfl⟩ := decomp w
  match ns with
  | [] => exact absurd h.1 (by rw [parse_short] <;> simp)
  | [a] => exact absurd h.1 (by rw [parse_short] <;> simp)
  | a :: t :: es =>
    rw [parse_full] at h
    obtain ⟨-, hk, hb, hc, hsum⟩ := h
    simp only at hk hb hc hsum
    subst hk
    rw [sum_map_eq_zero] at hb
    refine ⟨⟨a, t, fun i => es[i.val]'(by omega)⟩, ⟨?_, ?_⟩, ?_⟩
    · have : (List.ofFn (fun i : Fin (3 * a) => es[i.val]'(by omega))) = es := by
        apply List.ext_getElem <;> simp [hc]
      rw [← List.sum_ofFn, this]; simpa using hsum
    · intro i
      exact (badInc_eq_zero _ _).1 (hb _ (List.getElem_mem _))
    · have : (List.ofFn (fun i : Fin (3 * a) => es[i.val]'(by omega))) = es := by
        apply List.ext_getElem <;> simp [hc]
      simp [ThreePartition.code, this, unaryCode_cons]

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

theorem len_integerBlock (a : ℕ) : (integerBlock a).length = 5 * a + 5 := by
  simp [integerBlock, initiator, filler, terminator, List.length_flatten, List.sum_replicate]
  ring

theorem len_numberPieces (P : ThreePartition) :
    (numberPieces P).length = 5 * (∑ i, P.entry i) + 15 * P.s := by
  unfold numberPieces
  rw [List.length_flatMap]
  simp only [len_integerBlock, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp; ring

def Nval (staging s t : ℕ) : ℕ := 20 * (s * t) + 18 * t + 70 * s + 76 + 2 * staging

theorem noBound_eq (P : ThreePartition) (hP : P.Valid) (he : Even P.target) (staging : ℕ) :
    noBound P staging = Nval staging P.s P.target := by
  obtain ⟨m, hm⟩ := he
  unfold noBound baseBoard basePieces baseHeight Nval
  simp only [List.length_append, List.length_replicate, len_numberPieces, hP.1,
    List.length_cons, List.length_nil, hm]
  have : 3 * (m + m) / 2 = 3 * m := by omega
  rw [this]; ring

def lead : List Bool → ℕ
  | true :: l => lead l + 1
  | false :: _ => 0
  | [] => 0

def dropLead : List Bool → List Bool
  | true :: l => dropLead l
  | false :: l => false :: l
  | [] => []

theorem lead_le (l : List Bool) : lead l ≤ l.length := by
  induction l with
  | nil => simp [lead]
  | cons x l ih => cases x <;> simp [lead] <;> omega

theorem dropLead_len (l : List Bool) : (dropLead l).length ≤ l.length := by
  induction l with
  | nil => simp [dropLead]
  | cons x l ih => cases x <;> simp [dropLead] <;> omega

theorem lead_code (n : ℕ) (rest : List Bool) :
    lead (List.replicate n true ++ false :: rest) = n ∧
      dropLead (List.replicate n true ++ false :: rest) = false :: rest := by
  induction n with
  | zero => simp [lead, dropLead]
  | succ n ih => simp [List.replicate_succ, lead, dropLead, ih]

def loopLead (k : K) : StackProg K Bool :=
  .loop (fun h => decide (h 0 = some true)) (.seq (popProg 0) (pushProg k true))

theorem run_loopLead (k : K) (hk : k ≠ 0) : ∀ (l : List Bool) (b : K → List Bool) (r : K → ℕ),
    b 0 = l → r 0 = 0 →
    Run (loopLead k) (st b r)
      (st (Function.update b 0 (dropLead l)) (Function.update r k (r k + lead l)))
      (5 * lead l + 1) := by
  intro l
  induction l with
  | nil =>
    intro b r hb hr
    have := Run.loopF (p := .seq (popProg 0) (pushProg k true)) (s := st b r)
      (test := fun h => decide (h 0 = some true)) (by simp [st, hb, hr])
    refine this.congr ?_
    simp [dropLead, lead, ← hb]
  | cons x l ih =>
    intro b r hb hr
    cases x with
    | false =>
      have := Run.loopF (p := .seq (popProg 0) (pushProg k true)) (s := st b r)
        (test := fun h => decide (h 0 = some true)) (by simp [st, hb, hr])
      refine this.congr ?_
      simp [dropLead, lead, ← hb]
    | true =>
      have h1 := (run_popB b r 0 hr).seq (run_push _ r k)
      have h2 := ih (Function.update b 0 (b 0).tail) (Function.update r k (r k + 1))
        (by simp [hb]) (by simp [Function.update_of_ne (Ne.symm hk), hr])
      have := Run.loopT (test := fun h => decide (h 0 = some true)) (by simp [st, hb, hr]) h1 h2
      refine (this.congr ?_).mono (by simp [lead]; omega)
      simp [dropLead, lead]
      congr 1
      funext j; by_cases hj : j = k
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]

def e3546 : Fin 4 ↪ K := ⟨![3, 5, 4, 6], by decide⟩
def e5146 : Fin 4 ↪ K := ⟨![5, 1, 4, 6], by decide⟩
def e3146 : Fin 4 ↪ K := ⟨![3, 1, 4, 6], by decide⟩
def e2146 : Fin 4 ↪ K := ⟨![2, 1, 4, 6], by decide⟩

def progG (stg : ℕ) : StackProg K Bool :=
  .seq (pushProg 1 false) <| .seq (loopLead 2) <| .seq (popProg 0) <| .seq (loopLead 3) <|
  .seq (copyProg 2 4 6) <| .seq (repeatCopyProg e3546) <| .seq (pushN 4 20) <|
  .seq (repeatCopyProg e5146) <| .seq (pushN 4 18) <| .seq (repeatCopyProg e3146) <|
  .seq (pushN 4 70) <| .seq (repeatCopyProg e2146) (pushN 1 (76 + 2 * stg))

def gfun (stg : ℕ) (u : List Bool) : List Bool :=
  unaryCode [Nval stg (lead u) (lead (dropLead u).tail)]

theorem g_run (stg : ℕ) (u : List Bool) :
    ∃ S B, Run (progG stg) (st (fun j => if j = 0 then u else []) (fun _ => 0)) S B ∧
      S 1 = gfun stg u ∧ B ≤ 300 * (u.length + 1) ^ 2 + 4 * stg + 1000 := by
  refine ⟨_, _, Run.seq (run_pushB _ _ 1 false) <| Run.seq (run_loopLead 2 (by decide) u _ _ ?_ ?_) <|
    Run.seq (run_popB _ _ 0 ?_) <| Run.seq (run_loopLead 3 (by decide) _ _ _ rfl ?_) <|
    Run.seq (run_copy _ _ 2 4 6 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_repeat _ _ e3546 ?_ ?_ ?_ ?_) <| Run.seq (run_pushN _ 4 20 _) <|
    Run.seq (run_repeat _ _ e5146 ?_ ?_ ?_ ?_) <| Run.seq (run_pushN _ 4 18 _) <|
    Run.seq (run_repeat _ _ e3146 ?_ ?_ ?_ ?_) <| Run.seq (run_pushN _ 4 70 _) <|
    Run.seq (run_repeat _ _ e2146 ?_ ?_ ?_ ?_) (run_pushN _ 1 (76 + 2 * stg) _), ?_, ?_⟩
  all_goals try (simp [e3546, e5146, e3146, e2146, Function.update_apply]; done)
  · simp [e3546, e5146, e3146, e2146, Function.update_apply, st, gfun, unaryCode, Nval]
    ring_nf
  · simp [e3546, e5146, e3146, e2146, Function.update_apply]
    have h1 := lead_le u
    have h2 := lead_le (dropLead u).tail
    have h3 := dropLead_len u
    have h4 : (dropLead u).tail.length ≤ u.length := by simp; omega
    generalize lead u = a at *
    generalize lead (dropLead u).tail = c at *
    generalize u.length = L at *
    nlinarith

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

theorem g_polytime (stg : ℕ) : PolyTimeComputable (gfun stg) := by
  obtain ⟨k, hk⟩ := polynomial_absorb 300 2 (4 * stg + 1000)
  refine stack_program_polytime (progG stg) 0 1 (gfun stg) k (fun u => ?_)
  obtain ⟨S, B, ⟨n, hn, he⟩, hS, hB⟩ := g_run stg u
  exact ⟨S, n, by have := hk u.length; omega, he, hS⟩

theorem gfun_code (stg : ℕ) (P : ThreePartition) :
    gfun stg P.code = unaryCode [Nval stg P.s P.target] := by
  have hc : P.code = List.replicate P.s true ++ false ::
      (List.replicate P.target true ++ false :: unaryCode (List.ofFn P.entry)) := by
    simp [ThreePartition.code, unaryCode_cons]
  rw [gfun, hc, (lead_code _ _).1, (lead_code _ _).2, List.tail_cons, (lead_code _ _).1]

/-! ### The normalization program -/

def Clean (b : K → List Bool) : Prop := ∀ j : K, 2 ≤ j.val → j.val ≤ 13 → b j = []

theorem Clean.upd {b : K → List Bool} (hb : Clean b) (j : K) (hj : j.val < 2 ∨ 13 < j.val)
    (x : List Bool) : Clean (Function.update b j x) := by
  intro i h1 h2
  have : i ≠ j := by rintro rfl; omega
  rw [Function.update_of_ne this]; exact hb i h1 h2

def condPush (j k : K) : StackProg K Bool :=
  .branch (fun h => (h j).isSome) noop (pushProg k true)

theorem run_condPush (b : K → List Bool) (r : K → ℕ) (j k : K) (hbj : b j = []) :
    Run (condPush j k) (st b r) (st b (Function.update r k (r k + if 0 < r j then 0 else 1))) 2 := by
  by_cases h : 0 < r j
  · have := Run.branchT (q := pushProg k true) (test := fun h => (h j).isSome)
      (by simp [head_st_nil r hbj, h]) (run_noop (st b r))
    refine this.congr ?_
    simp [h]
  · have := Run.branchF (p := noop) (test := fun h => (h j).isSome)
      (by simp [head_st_nil r hbj, h]) (run_push b r k)
    refine this.congr ?_
    simp [h]

def chk1 : StackProg K Bool :=
  .seq (copyProg 2 10 12) <| .seq (copyProg 2 10 12) <| .seq (copyProg 2 10 12) <|
  .seq (copyProg 2 10 12) <| .seq (copyProg 4 11 12) <| .seq (syncPopProg 10 11) <|
  .seq (condPush 10 7) <| .seq (clearProg 10) (clearProg 11)

def chk2 : StackProg K Bool :=
  .seq (copyProg 2 10 12) <| .seq (copyProg 2 10 12) <|
  .seq (copyProg 4 11 12) <| .seq (syncPopProg 10 11) <|
  .seq (condPush 11 7) <| .seq (clearProg 10) (clearProg 11)

theorem run_chk1 (b : K → List Bool) (hb : Clean b) (r : K → ℕ)
    (h10 : r 10 = 0) (h11 : r 11 = 0) (h12 : r 12 = 0) :
    Run chk1 (st b r) (st b (Function.update r 7 (r 7 + if r 4 < 4 * r 2 then 0 else 1)))
      (60 * r 2 + 20 * r 4 + 40) := by
  refine Run.mono (Run.congr (Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 4 11 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_sync _ _ 10 11 (by decide) ?_ ?_) <|
    Run.seq (run_condPush _ _ 10 7 ?_) <|
    Run.seq (run_clear _ _ 10 ?_) (run_clear _ _ 11 ?_)) ?_) ?_
  all_goals try (first | exact hb _ (by decide) (by decide) | simp [Function.update_apply, h12]; done)
  · congr 1; funext k
    fin_cases k <;> simp [Function.update_apply, h10, h11, h12] <;> split_ifs <;> omega
  · simp [Function.update_apply, h10, h11, h12]; omega

theorem run_chk2 (b : K → List Bool) (hb : Clean b) (r : K → ℕ)
    (h10 : r 10 = 0) (h11 : r 11 = 0) (h12 : r 12 = 0) :
    Run chk2 (st b r) (st b (Function.update r 7 (r 7 + if 2 * r 2 < r 4 then 0 else 1)))
      (60 * r 2 + 20 * r 4 + 40) := by
  refine Run.mono (Run.congr (Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 4 11 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_sync _ _ 10 11 (by decide) ?_ ?_) <|
    Run.seq (run_condPush _ _ 11 7 ?_) <|
    Run.seq (run_clear _ _ 10 ?_) (run_clear _ _ 11 ?_)) ?_) ?_
  all_goals try (first | exact hb _ (by decide) (by decide) | simp [Function.update_apply, h12]; done)
  · congr 1; funext k
    fin_cases k <;> simp [Function.update_apply, h10, h11, h12] <;> split_ifs <;> omega
  · simp [Function.update_apply, h10, h11, h12]; omega

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

def toR (p : PS) : K → ℕ := fun k =>
  if k = 2 then p.cur else if k = 3 then p.s else if k = 4 then p.t else if k = 5 then p.cnt
  else if k = 6 then p.sum else if k = 7 then p.bad else if k = 8 then (if p.f1 then 1 else 0)
  else if k = 9 then (if p.f2 then 1 else 0) else 0

def ENTRY : StackProg K Bool :=
  .seq chk1 <| .seq chk2 <| .seq (pushProg 5 true) (clearProg 2)

theorem run_entry (b : K → List Bool) (hb : Clean b) (r : K → ℕ)
    (h10 : r 10 = 0) (h11 : r 11 = 0) (h12 : r 12 = 0) :
    Run ENTRY (st b r) (st b (Function.update (Function.update (Function.update r 7
      (r 7 + badInc (r 4) (r 2))) 5 (r 5 + 1)) 2 0)) (130 * r 2 + 50 * r 4 + 100) := by
  refine Run.mono (Run.congr (Run.seq (run_chk1 b hb r h10 h11 h12) <|
    Run.seq (run_chk2 b hb _ ?_ ?_ ?_) <| Run.seq (run_push _ _ 5) (run_clear _ _ 2 ?_)) ?_) ?_
  all_goals try (first | exact hb _ (by decide) (by decide) | simp [Function.update_apply, h10, h11, h12]; done)
  · congr 1; funext k
    fin_cases k <;> simp [Function.update_apply, badInc] <;> omega
  · simp [Function.update_apply]; omega

def TB : StackProg K Bool :=
  .seq (popProg 0) <| .seq (pushProg 2 true) (.branch (fun h => (h 9).isSome) (pushProg 6 true) noop)

def FB : StackProg K Bool :=
  .seq (popProg 0) (.branch (fun h => (h 8).isSome)
    (.branch (fun h => (h 9).isSome) ENTRY
      (.seq (transferProg 2 (fun k => decide (k = 4))) (pushProg 9 true)))
    (.seq (transferProg 2 (fun k => decide (k = 3))) (pushProg 8 true)))

def BODY : StackProg K Bool := .branch (fun h => decide (h 0 = some true)) TB FB

theorem run_body (b : K → List Bool) (hb : Clean b) (x : Bool) (rest : List Bool)
    (hb0 : b 0 = x :: rest) (p : PS) :
    Run BODY (st b (toR p)) (st (Function.update b 0 rest) (toR (pstep p x)))
      (200 * (p.cur + p.t) + 200) := by
  have hb' : Clean (Function.update b 0 rest) := hb.upd 0 (by decide) _
  have e2 := hb' 2 (by decide) (by decide)
  have e3 := hb' 3 (by decide) (by decide)
  have e8 := hb' 8 (by decide) (by decide)
  have e9 := hb' 9 (by decide) (by decide)
  have htl : Function.update b 0 (b 0).tail = Function.update b 0 rest := by simp [hb0]
  obtain ⟨cur, s, t, cnt, sum, bad, f1, f2⟩ := p
  cases x with
  | true =>
    cases f2 with
    | true =>
      refine Run.mono (Run.congr (Run.branchT ?_ (Run.seq (run_popB _ _ 0 ?_) <|
        Run.seq (run_push _ _ 2) (Run.branchT ?_ (run_push _ _ 6)))) ?_) ?_
      · simp [st, toR, hb0]
      · simp [toR]
      · rw [htl]; simp [head_st_nil _ e9, Function.update_apply, toR]
      · rw [htl]; congr 1; funext k
        fin_cases k <;> simp [Function.update_apply, toR, pstep]
      · simp
    | false =>
      refine Run.mono (Run.congr (Run.branchT ?_ (Run.seq (run_popB _ _ 0 ?_) <|
        Run.seq (run_push _ _ 2) (Run.branchF ?_ (run_noop _)))) ?_) ?_
      · simp [st, toR, hb0]
      · simp [toR]
      · rw [htl]; simp [head_st_nil _ e9, Function.update_apply, toR]
      · rw [htl]; congr 1; funext k
        fin_cases k <;> simp [Function.update_apply, toR, pstep]
      · simp
  | false =>
    cases f1 with
    | true =>
      cases f2 with
      | true =>
        refine Run.mono (Run.congr (Run.branchF ?_ (Run.seq (run_popB _ _ 0 ?_) <|
          Run.branchT ?_ (Run.branchT ?_ (run_entry _ (htl ▸ hb') _ ?_ ?_ ?_)))) ?_) ?_
        · simp [st, toR, hb0]
        · simp [toR]
        · rw [htl]; simp [head_st_nil _ e8, toR]
        · rw [htl]; simp [head_st_nil _ e9, toR]
        all_goals try (simp [toR]; done)
        · rw [htl]; congr 1; funext k
          fin_cases k <;> simp [Function.update_apply, toR, pstep]
        · simp [toR]; omega
      | false =>
        refine Run.mono (Run.congr (Run.branchF ?_ (Run.seq (run_popB _ _ 0 ?_) <|
          Run.branchT ?_ (Run.branchF ?_ (Run.seq (run_move _ _ 2 4 (by decide) ?_)
            (run_push _ _ 9))))) ?_) ?_
        · simp [st, toR, hb0]
        · simp [toR]
        · rw [htl]; simp [head_st_nil _ e8, toR]
        · rw [htl]; simp [head_st_nil _ e9, toR]
        · rw [htl]; exact e2
        · rw [htl]; congr 1; funext k
          fin_cases k <;> simp [Function.update_apply, toR, pstep]
        · simp [toR]; omega
    | false =>
      refine Run.mono (Run.congr (Run.branchF ?_ (Run.seq (run_popB _ _ 0 ?_) <|
        Run.branchF ?_ (Run.seq (run_move _ _ 2 3 (by decide) ?_)
            (run_push _ _ 8)))) ?_) ?_
      · simp [st, toR, hb0]
      · simp [toR]
      · rw [htl]; simp [head_st_nil _ e8, toR]
      · rw [htl]; exact e2
      · rw [htl]; congr 1; funext k
        fin_cases k <;> simp [Function.update_apply, toR, pstep]
      · simp [toR]; omega

theorem pstep_ct (p : PS) (x : Bool) : (pstep p x).cur + (pstep p x).t ≤ p.cur + p.t + 1 := by
  unfold pstep; split_ifs <;> simp <;> omega

def LOOP : StackProg K Bool := .loop (fun h => (h 0).isSome) BODY

theorem run_loop (L : ℕ) : ∀ (rest : List Bool) (b : K → List Bool) (p : PS), Clean b →
    b 0 = rest → p.cur + p.t + rest.length ≤ L →
    Run LOOP (st b (toR p)) (st (Function.update b 0 []) (toR (rest.foldl pstep p)))
      (rest.length * (200 * L + 203) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro b p hb hb0 _
    have := Run.loopF (p := BODY) (s := st b (toR p)) (test := fun h => (h 0).isSome)
      (by simp [st, toR, hb0])
    refine (this.congr ?_).mono (by simp)
    have : Function.update b 0 [] = b := by rw [← hb0]; exact Function.update_eq_self 0 b
    simp [this]
  | cons x rest ih =>
    intro b p hb hb0 hL
    have h2 := ih (Function.update b 0 rest) (pstep p x) (hb.upd 0 (by decide) _) (by simp)
      (by have := pstep_ct p x; simp at hL; omega)
    have := Run.loopT (test := fun h => (h 0).isSome) (by simp [st, toR, hb0])
      (run_body b hb x rest hb0 p) h2
    refine (this.congr ?_).mono ?_
    · simp
    · simp only [List.length_cons, add_one_mul] at hL ⊢
      omega

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

def gstep (m : ℕ) (q : ℕ × List Bool) (x : Bool) : ℕ × List Bool :=
  if x then (q.1 + 1, q.2) else (0, false :: List.replicate (q.1 * m) true ++ q.2)

theorem gfold_rep (m n : ℕ) : ∀ (c : ℕ) (o : List Bool),
    (List.replicate n true).foldl (gstep m) (c, o) = (c + n, o) := by
  induction n with
  | zero => intro c o; simp
  | succ n ih =>
    intro c o
    rw [List.replicate_succ, List.foldl_cons, gstep, if_pos rfl, ih]
    simp; omega

theorem gen_fold (m : ℕ) (rest : List ℕ) : ∀ (n₀ c : ℕ) (o : List Bool),
    (unaryCode (n₀ :: rest)).reverse.foldl (gstep m) (c, o) =
      (n₀, false :: unaryCode (rest.map (· * m)) ++ List.replicate (c * m) true ++ o) := by
  induction rest with
  | nil =>
    intro n₀ c o
    simp [unaryCode, gstep, gfold_rep]
  | cons n₁ rest ih =>
    intro n₀ c o
    have : (unaryCode (n₀ :: n₁ :: rest)).reverse =
        (unaryCode (n₁ :: rest)).reverse ++ false :: List.replicate n₀ true := by
      rw [unaryCode_cons n₀]; simp
    rw [this, List.foldl_append, ih, List.foldl_cons, gstep, if_neg (by simp), gfold_rep]
    simp [unaryCode_cons]

def e11 : Fin 4 ↪ K := ⟨![11, 1, 2, 12], by decide⟩

def GBODY : StackProg K Bool :=
  .branch (fun h => decide (h 15 = some true)) (.seq (popProg 15) (pushProg 2 true))
    (.seq (popProg 15) (.seq (repeatCopyProg e11) (pushProg 1 false)))

def GLOOP : StackProg K Bool := .loop (fun h => (h 15).isSome) GBODY

theorem run_gloop (m L : ℕ) : ∀ (rev : List Bool) (b : K → List Bool) (r : K → ℕ), Clean b →
    b 15 = rev → r 15 = 0 → r 1 = 0 → r 12 = 0 → r 11 = m → r 2 + rev.length ≤ L →
    Run GLOOP (st b r)
      (st (Function.update (Function.update b 15 []) 1 (rev.foldl (gstep m) (r 2, b 1)).2)
        (Function.update r 2 (rev.foldl (gstep m) (r 2, b 1)).1))
      (rev.length * ((6 * m + 7) * L + 10) + 1) := by
  intro rev
  induction rev with
  | nil =>
    intro b r hb h15 r15 r1 r12 r11 hL
    have := Run.loopF (p := GBODY) (s := st b r) (test := fun h => (h 15).isSome)
      (by simp [st, h15, r15])
    refine (this.congr ?_).mono (by simp)
    have : Function.update b 15 [] = b := by rw [← h15]; exact Function.update_eq_self 15 b
    simp [this]
  | cons x rest ih =>
    intro b r hb h15 r15 r1 r12 r11 hL
    have htl : Function.update b 15 (b 15).tail = Function.update b 15 rest := by simp [h15]
    have hb' : Clean (Function.update b 15 rest) := hb.upd 15 (by decide) _
    simp only [List.length_cons] at hL
    cases x with
    | true =>
      have h1 := (run_popB b r 15 r15).seq (run_push _ r 2)
      rw [htl] at h1
      have h1' : Run GBODY (st b r) _ _ := Run.branchT (by simp [st, h15, r15]) h1
      have h2 := ih (Function.update b 15 rest) (Function.update r 2 (r 2 + 1)) hb' (by simp)
        (by simp [r15]) (by simp [r1]) (by simp [r12]) (by simp [r11]) (by simp; omega)
      have := Run.loopT (test := fun h => (h 15).isSome) (by simp [st, h15, r15]) h1' h2
      refine (this.congr ?_).mono ?_
      · simp [gstep]
      · simp only [List.length_cons, add_one_mul]
        have : (6 * m + 7) * 0 ≤ (6 * m + 7) * L := Nat.mul_le_mul_left _ (Nat.zero_le _)
        nlinarith
    | false =>
      have h1 := (run_popB b r 15 r15).seq ((run_repeat _ r e11 ?_ ?_ ?_ ?_).seq
        (run_pushB _ _ 1 false))
      rotate_left
      · simpa [e11] using hb 11 (by decide) (by decide)
      · simpa [e11] using hb 2 (by decide) (by decide)
      · simpa [e11] using hb 12 (by decide) (by decide)
      · simpa [e11] using r12
      simp only [htl] at h1
      have h1' : Run GBODY (st b r) _ _ := Run.branchF (by simp [st, h15, r15]) h1
      have := Run.loopT (test := fun h => (h 15).isSome) (by simp [st, h15, r15]) h1'
        (ih _ _ ((hb'.upd 1 (by decide) _)) (by simp) (by simp [e11, Function.update_apply, r15])
        (by simp) (by simp [e11, Function.update_apply, r12])
        (by simp [e11, Function.update_apply, r11]) (by simp [e11, Function.update_apply]; omega))
      refine (this.congr ?_).mono ?_
      · simp only [e11, Function.Embedding.coeFn_mk, List.foldl_cons]
        congr 1
        · funext j
          simp [Function.update_apply, gstep, st, r1, r11]
          split_ifs <;> simp_all
        · funext j
          simp [Function.update_apply, gstep, st, r1, r11]
          split_ifs <;> simp_all
      · simp only [e11, Function.Embedding.coeFn_mk, List.length_cons, add_one_mul]
        simp [r11]
        have : (6 * m + 7) * r 2 ≤ (6 * m + 7) * L := Nat.mul_le_mul_left _ (by omega)
        nlinarith

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

theorem pstep_bound (p : PS) (x : Bool) :
    (pstep p x).cur + (pstep p x).s + (pstep p x).t ≤ p.cur + p.s + p.t + 1 ∧
    (pstep p x).cnt ≤ p.cnt + 1 ∧ (pstep p x).sum ≤ p.sum + 1 := by
  unfold pstep; split_ifs <;> simp <;> omega

theorem fold_bound : ∀ (l : List Bool) (p : PS),
    (l.foldl pstep p).cur + (l.foldl pstep p).s + (l.foldl pstep p).t ≤
      p.cur + p.s + p.t + l.length ∧
    (l.foldl pstep p).cnt ≤ p.cnt + l.length ∧ (l.foldl pstep p).sum ≤ p.sum + l.length := by
  intro l
  induction l with
  | nil => intro p; simp
  | cons x l ih =>
    intro p
    have h1 := ih (pstep p x)
    have h2 := pstep_bound p x
    simp only [List.foldl_cons, List.length_cons]
    omega

def eTP : Fin 4 ↪ K := ⟨![4, 11, 13, 12], by decide⟩
def eS6 : Fin 4 ↪ K := ⟨![3, 11, 13, 12], by decide⟩

def TP : StackProg K Bool :=
  .seq (copyProg 3 10 12) <| .seq (copyProg 3 10 12) <| .seq (copyProg 3 10 12) <|
  .seq (syncPopProg 10 5) <| .seq (copyProg 3 13 12) <| .seq (repeatCopyProg eTP)
    (syncPopProg 11 6)

def tpR (q : PS) : K → ℕ :=
  Function.update (Function.update (Function.update (Function.update (toR q)
    10 (3 * q.s - min (3 * q.s) q.cnt)) 5 (q.cnt - min (3 * q.s) q.cnt))
    11 (q.s * q.t - min (q.s * q.t) q.sum)) 6 (q.sum - min (q.s * q.t) q.sum)

theorem run_TP (b : K → List Bool) (hb : Clean b) (q : PS) :
    Run TP (st b (toR q)) (st b (tpR q))
      (31 * q.s + 6 * (q.t * q.s) + 3 * q.cnt + 3 * q.sum + 40) := by
  refine Run.mono (Run.congr (Run.seq (run_copy _ _ 3 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 3 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 3 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_sync _ _ 10 5 (by decide) ?_ ?_) <|
    Run.seq (run_copy _ _ 3 13 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_repeat _ _ eTP ?_ ?_ ?_ ?_) (run_sync _ _ 11 6 (by decide) ?_ ?_)) ?_) ?_
  all_goals try (first | exact hb _ (by decide) (by decide) |
    simp [eTP]; exact hb _ (by decide) (by decide) |
    simp [Function.update_apply, toR, eTP]; done)
  · congr 1; funext k
    fin_cases k <;> simp [Function.update_apply, toR, tpR, eTP] <;> omega
  · simp [Function.update_apply, toR, eTP]
    have := Nat.min_le_right (q.s + (q.s + q.s)) q.cnt
    have := Nat.min_le_right (q.s * q.t) q.sum
    nlinarith

instance : DecidablePred PS.ok := fun q => by unfold PS.ok; infer_instance

def VT (h : K → Option Bool) : Bool :=
  (h 9).isSome && (h 2).isNone && (h 7).isNone && (h 10).isNone && (h 5).isNone &&
    (h 11).isNone && (h 6).isNone

theorem VT_eq (b : K → List Bool) (hb : Clean b) (q : PS) :
    VT (fun k => (st b (tpR q) k).head?) = decide q.ok := by
  have H : ∀ k : K, 2 ≤ k.val → k.val ≤ 13 →
      (st b (tpR q) k).head? = if 0 < tpR q k then some true else none :=
    fun k h1 h2 => head_st_nil _ (hb k h1 h2)
  simp only [VT, H 9 (by decide) (by decide), H 2 (by decide) (by decide),
    H 7 (by decide) (by decide), H 10 (by decide) (by decide), H 5 (by decide) (by decide),
    H 11 (by decide) (by decide), H 6 (by decide) (by decide)]
  simp only [tpR, toR, PS.ok, Function.update_apply]
  clear H
  rcases q with ⟨cur, s, t, cnt, sum, bad, f1, f2⟩
  cases f2 <;> simp <;> split_ifs <;> simp <;> omega

def GEN : StackProg K Bool :=
  .seq (pushN 13 6) <| .seq (repeatCopyProg eS6) <|
  .seq (transferProg 14 (fun k => decide (k = 15))) <|
  .seq GLOOP (transferProg 2 (fun k => decide (k = 1)))

theorem len_unaryCode_ge (n : ℕ) (rest : List ℕ) : n + 1 ≤ (unaryCode (n :: rest)).length := by
  simp [unaryCode_cons]

theorem run_GEN (b : K → List Bool) (hb : Clean b) (r : K → ℕ) (h1 : r 1 = 0) (h2 : r 2 = 0)
    (h11 : r 11 = 0) (h12 : r 12 = 0) (h13 : r 13 = 0) (h14 : r 14 = 0) (h15 : r 15 = 0)
    (hb1 : b 1 = []) (hb15 : b 15 = []) (n₀ : ℕ) (rest : List ℕ)
    (hw : b 14 = unaryCode (n₀ :: rest)) (L : ℕ) (hL : (b 14).length ≤ L) (hs : r 3 ≤ L) :
    ∃ S, Run GEN (st b r) S (100 * (L + 1) ^ 3) ∧
      S 1 = List.replicate n₀ true ++ false :: unaryCode (rest.map (· * (6 * r 3))) := by
  have hn : n₀ + 1 ≤ L := by have := len_unaryCode_ge n₀ rest; rw [← hw] at this; omega
  refine ⟨_, Run.mono (Run.seq (run_pushN b 13 6 r) <| Run.seq (run_repeat _ _ eS6 ?_ ?_ ?_ ?_) <|
    Run.seq (run_moveB _ _ 14 15 (by decide) ?_ ?_) <|
    Run.seq (run_gloop (6 * r 3) L ((b 14).reverse ++ b 15) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      (run_moveU _ _ 2 1 (by decide) ?_ ?_)) ?_, ?_⟩
  all_goals try (first | exact hb _ (by decide) (by decide) |
    simp [eS6]; exact hb _ (by decide) (by decide) |
    simp [Function.update_apply, eS6, h1, h2, h11, h12, h13, h14, h15, hb1, hb15]; done)
  · exact (hb.upd 14 (by decide) _).upd 15 (by decide) _
  · simp [Function.update_apply, eS6, h2, h13, hb15]; omega
  · simp only [hw, hb15, List.append_nil, gen_fold]
    simp [Function.update_apply, eS6, h1, h2, h11, h12, h13, h14, h15, hb1, hb15]
    rw [hw] at hL
    have h36 : (6 * (6 * r 3) + 7) * L + 10 ≤ (36 * L + 7) * L + 10 := by
      have := Nat.mul_le_mul_right L (show 6 * (6 * r 3) + 7 ≤ 36 * L + 7 by omega)
      omega
    have hA := Nat.mul_le_mul hL h36
    generalize (unaryCode (n₀ :: rest)).length * ((6 * (6 * r 3) + 7) * L + 10) = P at hA ⊢
    generalize (unaryCode (n₀ :: rest)).length = X at hA hL ⊢
    have := Nat.zero_le (L ^ 3)
    have := Nat.zero_le (L ^ 2)
    nlinarith
  · simp only [hw, hb15, List.append_nil, gen_fold]
    simp [Function.update_apply, eS6, h1, h2, h11, h12, h13, h14, h15, hb1, hb15, st]

end NoBoundPf

namespace NoBoundPf
open TetrisHard.Rows

def TOP : StackProg K Bool :=
  .seq (copyProg 0 14 12) <| .seq LOOP <| .seq TP <|
  .branch VT (.branch (fun h => (h 3).isSome) GEN (pushL 1 yesInstance.scale.code))
    (pushL 1 noInstance.scale.code)

theorem rawInstance_pos (w : List Bool)
    (h : ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code) :
    rawInstance w = Classical.choose h := by
  unfold rawInstance; rw [dif_pos h]

theorem rawInstance_yes (w : List Bool)
    (h : ¬ ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code)
    (h' : ∃ P : ThreePartition, P.Valid ∧ w = P.code) :
    rawInstance w = yesInstance := by
  unfold rawInstance; rw [dif_neg h, if_pos h']

theorem rawInstance_no (w : List Bool)
    (h : ¬ ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code)
    (h' : ¬ ∃ P : ThreePartition, P.Valid ∧ w = P.code) :
    rawInstance w = noInstance := by
  unfold rawInstance; rw [dif_neg h, if_neg h']

theorem scale_code (P : ThreePartition) :
    P.scale.code = List.replicate P.s true ++ false ::
      unaryCode ((P.target :: List.ofFn P.entry).map (· * (6 * P.s))) := by
  simp only [ThreePartition.code, ThreePartition.scale, List.cons_append, List.nil_append,
    unaryCode_cons, List.map_cons, List.map_ofFn]
  congr 3
  · ring
  · rw [show (fun i => 6 * P.s * P.entry i) = ((fun x => x * (6 * P.s)) ∘ P.entry) from
      funext fun i => by simp only [Function.comp_apply]; ring]

theorem top_run (w : List Bool) :
    ∃ S B, Run TOP (st (fun j => if j = 0 then w else []) (fun _ => 0)) S B ∧
      S 1 = (normInstance w).code ∧
      B ≤ 1000 * (w.length + 1) ^ 3 +
        2 * (yesInstance.scale.code.length + noInstance.scale.code.length) + 100 := by
  set b0 : K → List Bool := fun j => if j = 0 then w else [] with hb0
  have hA := run_copyB b0 (fun _ => 0) 0 14 12 (by decide) (by decide) (by decide) rfl rfl
    (by simp [b0]) rfl
  have e0 : (fun _ : K => (0 : ℕ)) = toR p0 := by
    funext k; unfold toR p0; split_ifs <;> simp_all
  set bA := Function.update b0 14 (b0 0 ++ b0 14) with hbA_def
  have hbA : Clean bA := by
    intro j h1 h2
    have : j ≠ 14 := by rintro rfl; exact absurd h2 (by decide)
    rw [hbA_def, Function.update_of_ne this]
    have : j ≠ 0 := by rintro rfl; exact absurd h1 (by decide)
    simp [b0, this]
  have hB := run_loop w.length w bA p0 hbA (by simp [bA, b0]) (by simp [p0])
  rw [← e0] at hB
  set q := w.foldl pstep p0 with hq
  set b1 := Function.update bA 0 [] with hb1_def
  have hb1 : Clean b1 := hbA.upd 0 (by decide) _
  have hT := run_TP b1 hb1 q
  have hlen : (b0 0).length = w.length := by simp [b0]
  have hfb : q.cur + q.s + q.t ≤ w.length ∧ q.cnt ≤ w.length ∧ q.sum ≤ w.length := by
    have := fold_bound w p0
    rw [hq]; simp only [p0] at this ⊢; omega
  have hts : q.t * q.s ≤ w.length * w.length := Nat.mul_le_mul (by omega) (by omega)
  have hb1_1 : b1 1 = [] := by simp [b1, bA, b0]
  have hb1_15 : b1 15 = [] := by simp [b1, bA, b0]
  have hb1_14 : b1 14 = w := by simp [b1, bA, b0]
  by_cases hok : q.ok
  · have hVT : VT (fun k => (st b1 (tpR q) k).head?) = true := by
      rw [VT_eq b1 hb1 q]; simp [hok]
    by_cases hs : 0 < q.s
    · obtain ⟨P, hPv, hPw⟩ := parse_ok w hok
      have hex : ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code :=
        ⟨P, hPv, by have := (parse_code P hPv).2.1; rw [← hPw, ← hq] at this; omega, hPw⟩
      obtain ⟨hv', hs', hw'⟩ := Classical.choose_spec hex
      set P' := Classical.choose hex with hP'
      have hpc := parse_code P' hv'
      rw [← hw'] at hpc
      obtain ⟨-, hqs, hqt⟩ := hpc
      rw [← hq] at hqs hqt
      obtain ⟨hf2, hcur, hbad, hcnt, hsum⟩ := hok
      obtain ⟨S, hG, hS⟩ := run_GEN b1 hb1 (tpR q)
        (by simp [tpR, toR]) (by simp [tpR, toR, hcur]) (by simp [tpR, toR, hsum])
        (by simp [tpR, toR]) (by simp [tpR, toR]) (by simp [tpR, toR]) (by simp [tpR, toR])
        hb1_1 hb1_15 P'.s (P'.target :: List.ofFn P'.entry)
        (by rw [hb1_14, hw']; simp [ThreePartition.code]) w.length (by rw [hb1_14])
        (by simp [tpR, toR]; omega)
      refine ⟨S, _, hA.seq (hB.seq (hT.seq (Run.branchT hVT (Run.branchT ?_ hG)))), ?_, ?_⟩
      · simp [head_st_nil _ (hb1 3 (by decide) (by decide)), tpR, toR, hs]
      · rw [hS, normInstance, rawInstance_pos w hex, ← hP', scale_code]
        simp [tpR, toR, hqs]
      · rw [hlen]
        generalize yesInstance.scale.code.length = Y
        generalize noInstance.scale.code.length = Nn
        clear hA hB hT
        obtain ⟨hf1, hf2', hf3⟩ := hfb
        have := Nat.zero_le (w.length ^ 3)
        have := Nat.zero_le (w.length ^ 2)
        nlinarith
    · have hnex : ¬ ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code := by
        rintro ⟨P, hv, hps, rfl⟩
        have := (parse_code P hv).2.1
        rw [← hq] at this; omega
      have hY := run_pushL 1 yesInstance.scale.code b1 (tpR q) (by simp [tpR, toR])
      refine ⟨_, _, hA.seq (hB.seq (hT.seq (Run.branchT hVT (Run.branchF ?_ hY)))), ?_, ?_⟩
      · simp [head_st_nil _ (hb1 3 (by decide) (by decide)), tpR, toR, hs]
      · rw [normInstance, rawInstance_yes w hnex (parse_ok w hok)]
        simp [st, tpR, toR, hb1_1]
      · rw [hlen]
        generalize yesInstance.scale.code.length = Y
        generalize noInstance.scale.code.length = Nn
        clear hA hB hT
        obtain ⟨hf1, hf2', hf3⟩ := hfb
        have := Nat.zero_le (w.length ^ 3)
        have := Nat.zero_le (w.length ^ 2)
        nlinarith
  · have hVT : VT (fun k => (st b1 (tpR q) k).head?) = false := by
      rw [VT_eq b1 hb1 q]; simp [hok]
    have hnex' : ¬ ∃ P : ThreePartition, P.Valid ∧ w = P.code := by
      rintro ⟨P, hv, rfl⟩
      exact hok (parse_code P hv).1
    have hnex : ¬ ∃ P : ThreePartition, P.Valid ∧ 0 < P.s ∧ w = P.code := by
      rintro ⟨P, hv, -, h⟩; exact hnex' ⟨P, hv, h⟩
    have hN := run_pushL 1 noInstance.scale.code b1 (tpR q) (by simp [tpR, toR])
    refine ⟨_, _, hA.seq (hB.seq (hT.seq (Run.branchF hVT hN))), ?_, ?_⟩
    · rw [normInstance, rawInstance_no w hnex hnex']
      simp [st, tpR, toR, hb1_1]
    · rw [hlen]
      generalize yesInstance.scale.code.length = Y
      generalize noInstance.scale.code.length = Nn
      clear hA hB hT
      obtain ⟨hf1, hf2', hf3⟩ := hfb
      have := Nat.zero_le (w.length ^ 3)
      have := Nat.zero_le (w.length ^ 2)
      nlinarith

theorem normCode_polytime :
    PolyTimeComputable (fun w : List Bool => (normInstance w).code) := by
  obtain ⟨k, hk⟩ := polynomial_absorb 1000 3
    (2 * (yesInstance.scale.code.length + noInstance.scale.code.length) + 100)
  refine stack_program_polytime TOP 0 1 _ k (fun w => ?_)
  obtain ⟨S, B, ⟨n, hn, he⟩, hS, hB⟩ := top_run w
  exact ⟨S, n, by have := hk w.length; omega, he, hS⟩

theorem scale_valid (P : ThreePartition) (hP : P.Valid) : P.scale.Valid := by
  obtain ⟨hs, hi⟩ := hP
  refine ⟨?_, fun i => ?_⟩
  · show (∑ i : Fin (3 * P.s), 6 * P.s * P.entry i) = P.s * (6 * P.s * P.target)
    rw [← Finset.mul_sum, hs]; ring
  · show 6 * P.s * P.target < 4 * (6 * P.s * P.entry i) ∧
      2 * (6 * P.s * P.entry i) < 6 * P.s * P.target
    have hpos : 0 < P.s := by
      rcases Nat.eq_zero_or_pos P.s with h | h
      · exact absurd i.2 (by simp [ThreePartition.scale, h])
      · exact h
    obtain ⟨h1, h2⟩ := hi i
    constructor <;> nlinarith

theorem yes_valid : yesInstance.Valid := by
  refine ⟨by simp [yesInstance]; first | decide | rfl, fun i => by simp [yesInstance]⟩

theorem no_valid : noInstance.Valid := by
  refine ⟨by simp [noInstance]; first | decide | rfl, fun i => ?_⟩
  change Fin 6 at i
  fin_cases i <;> simp [noInstance]

theorem normInstance_valid (w : List Bool) :
    (normInstance w).Valid ∧ Even (normInstance w).target := by
  refine ⟨scale_valid _ ?_, ⟨3 * (rawInstance w).s * (rawInstance w).target, by
    simp [normInstance, ThreePartition.scale]; ring⟩⟩
  unfold rawInstance
  split_ifs with h1 h2
  · exact (Classical.choose_spec h1).1
  · exact yes_valid
  · exact no_valid

end NoBoundPf

namespace GameEmit
open CookPvsNP

inductive Reg where
  | inp | s | t | th | st | bp | bbh | nb | pf | b | x | y | sq | s3 | ic | l | ss
  | w | w4 | w6 | t2 | r | h | out | c1 | c2 | o | zt | ot | g | buf | ta | tc | tz
  deriving DecidableEq

instance : Fintype Reg := Fintype.ofList
  [.inp, .s, .t, .th, .st, .bp, .bbh, .nb, .pf, .b, .x, .y, .sq, .s3, .ic, .l, .ss,
   .w, .w4, .w6, .t2, .r, .h, .out, .c1, .c2, .o, .zt, .ot, .g, .buf, .ta, .tc, .tz]
  (by intro x; cases x <;> simp)

abbrev St := Reg → List Bool

def size (s : St) : ℕ := ∑ k, (s k).length
def mu (s : St) : ℕ := size s + 1

theorem len_le_size (s : St) (k : Reg) : (s k).length ≤ size s :=
  Finset.single_le_sum (f := fun k => (s k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem len_lt_mu (s : St) (k : Reg) : (s k).length < mu s := by
  have := len_le_size s k; unfold mu; omega

theorem one_le_mu (s : St) : 1 ≤ mu s := by unfold mu; omega

theorem size_update (s : St) (k : Reg) (v : List Bool) :
    size (Function.update s k v) + (s k).length = size s + v.length := by
  unfold size
  have h1 : (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
    funext j; by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ (fun j => (s j).length) (Finset.mem_univ k)]
  ring

structure OpD where
  prog : StackProg Reg Bool
  sem : St → St
  C : ℕ
  d : ℕ
  exec : ∀ s, ∃ n, prog.Exec s (sem s) n ∧ n ≤ C * mu s ^ d
  grow : ∀ s, mu (sem s) ≤ C * mu s ^ d

theorem pow_mono_mu (s : St) {a b : ℕ} (h : a ≤ b) : mu s ^ a ≤ mu s ^ b :=
  Nat.pow_le_pow_right (one_le_mu s) h

structure Op where
  prog : StackProg Reg Bool
  sem : St → St
  poly : ∃ C d : ℕ, (∀ s, ∃ n, prog.Exec s (sem s) n ∧ n ≤ C * mu s ^ d) ∧
    (∀ s, mu (sem s) ≤ C * mu s ^ d)

def OpD.toOp (o : OpD) : Op := ⟨o.prog, o.sem, ⟨o.C, o.d, o.exec, o.grow⟩⟩

def Op.seq (o1 o2 : Op) : Op where
  prog := .seq o1.prog o2.prog
  sem := fun s => o2.sem (o1.sem s)
  poly := by
    obtain ⟨C1, d1, ex1, gr1⟩ := o1.poly
    obtain ⟨C2, d2, ex2, gr2⟩ := o2.poly
    have key : ∀ s, C2 * mu (o1.sem s) ^ d2 ≤ C2 * C1 ^ d2 * mu s ^ (d1 * (d2 + 1)) := by
      intro s
      calc C2 * mu (o1.sem s) ^ d2 ≤ C2 * (C1 * mu s ^ d1) ^ d2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (gr1 s) _)
        _ = C2 * C1 ^ d2 * mu s ^ (d1 * d2) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ _ := Nat.mul_le_mul_left _ (pow_mono_mu s (Nat.mul_le_mul_left _ (by omega)))
    refine ⟨C1 + 1 + C2 * C1 ^ d2, d1 * (d2 + 1), fun s => ?_, fun s => ?_⟩
    · obtain ⟨n1, h1, b1⟩ := ex1 s
      obtain ⟨n2, h2, b2⟩ := ex2 (o1.sem s)
      refine ⟨n1 + 1 + n2, StackProg.Exec.seq h1 h2, ?_⟩
      have k := key s
      have e1 : mu s ^ d1 ≤ mu s ^ (d1 * (d2 + 1)) :=
        pow_mono_mu s (Nat.le_mul_of_pos_right _ (by omega))
      have e0 : 1 ≤ mu s ^ (d1 * (d2 + 1)) := Nat.one_le_pow _ _ (one_le_mu s)
      have e2 := Nat.mul_le_mul_left C1 e1
      calc n1 + 1 + n2 ≤ C1 * mu s ^ (d1 * (d2 + 1)) + mu s ^ (d1 * (d2 + 1)) +
            C2 * C1 ^ d2 * mu s ^ (d1 * (d2 + 1)) := by omega
        _ = (C1 + 1 + C2 * C1 ^ d2) * mu s ^ (d1 * (d2 + 1)) := by ring
    · have k := key s
      have g2 := gr2 (o1.sem s)
      calc mu (o2.sem (o1.sem s)) ≤ C2 * C1 ^ d2 * mu s ^ (d1 * (d2 + 1)) := by omega
        _ ≤ (C1 + 1 + C2 * C1 ^ d2) * mu s ^ (d1 * (d2 + 1)) :=
            Nat.mul_le_mul_right _ (by omega)

def skipProg : StackProg Reg Bool := .act (fun _ _ => .keep)

theorem skip_exec (s : St) : skipProg.Exec s s 1 := by
  have h := StackProg.Exec.act
    (fun (_ : Reg → Option Bool) (_ : Reg) => (StackAct.keep : StackAct Bool)) s
  have e : StackProg.applyAct
      (fun (_ : Reg → Option Bool) (_ : Reg) => (StackAct.keep : StackAct Bool)) s = s := by
    funext k; rfl
  rw [e] at h; exact h

def skipD : OpD where
  prog := skipProg
  sem := id
  C := 1
  d := 1
  exec := fun s => ⟨1, skip_exec s, by have := one_le_mu s; simpa using this⟩
  grow := fun s => by simp

def Op.skip : Op := skipD.toOp

def opList : List Op → Op
  | [] => Op.skip
  | o :: os => o.seq (opList os)

theorem opList_nil_sem (s : St) : (opList []).sem s = s := rfl
theorem opList_cons_sem (o : Op) (os : List Op) (s : St) :
    (opList (o :: os)).sem s = (opList os).sem (o.sem s) := rfl

/-! ### Primitive operations -/

def pushOpD (k : Reg) (b : Bool) : OpD where
  prog := pushProg k b
  sem := fun s => Function.update s k (b :: s k)
  C := 2
  d := 1
  exec := fun s => ⟨1, (stack_basic_macros k s).1 b, by have := one_le_mu s; simp; omega⟩
  grow := fun s => by
    have := size_update s k (b :: s k)
    have := one_le_mu s
    simp at *; unfold mu at *; omega

def pushOp (k : Reg) (b : Bool) : Op := (pushOpD k b).toOp

def popOpD (k : Reg) : OpD where
  prog := popProg k
  sem := fun s => Function.update s k (s k).tail
  C := 1
  d := 1
  exec := fun s => ⟨1, (stack_basic_macros k s).2.1, by have := one_le_mu s; simp; omega⟩
  grow := fun s => by
    have := size_update s k (s k).tail
    have : (s k).tail.length ≤ (s k).length := by simp
    simp; unfold mu; omega

def popOp (k : Reg) : Op := (popOpD k).toOp

def clearOpD (k : Reg) : OpD where
  prog := clearProg k
  sem := fun s => Function.update s k []
  C := 4
  d := 1
  exec := fun s => ⟨_, (stack_basic_macros k s).2.2, by
    have := len_lt_mu s k; simp; omega⟩
  grow := fun s => by
    have := size_update s k []
    have := one_le_mu s
    simp at *; unfold mu at *; omega

def clearOp (k : Reg) : Op := (clearOpD k).toOp

def pushRevProg (k : Reg) : List Bool → StackProg Reg Bool
  | [] => skipProg
  | b :: l => .seq (pushProg k b) (pushRevProg k l)

theorem pushRev_exec (k : Reg) (l : List Bool) (s : St) :
    (pushRevProg k l).Exec s (Function.update s k (l.reverse ++ s k)) (2 * l.length + 1) := by
  induction l generalizing s with
  | nil =>
    simp only [pushRevProg, List.reverse_nil, List.nil_append, Function.update_eq_self,
      List.length_nil]
    exact skip_exec s
  | cons b l ih =>
    have h1 := (stack_basic_macros k s).1 b
    have h2 := ih (Function.update s k (b :: s k))
    have := StackProg.Exec.seq h1 h2
    simp only [Function.update_idem, Function.update_self] at this
    have e1 : l.reverse ++ b :: s k = (b :: l).reverse ++ s k := by simp
    have e2 : 1 + 1 + (2 * l.length + 1) = 2 * (b :: l).length + 1 := by simp; ring
    rw [e1, e2] at this
    exact this

def pushListOpD (k : Reg) (l : List Bool) : OpD where
  prog := pushRevProg k l.reverse
  sem := fun s => Function.update s k (l ++ s k)
  C := 2 * l.length + 2
  d := 1
  exec := fun s => ⟨_, by simpa using pushRev_exec k l.reverse s, by
    have := one_le_mu s; simp; nlinarith⟩
  grow := fun s => by
    have := size_update s k (l ++ s k)
    have := one_le_mu s
    simp at *; unfold mu at *; nlinarith

def pushListOp (k : Reg) (l : List Bool) : Op := (pushListOpD k l).toOp

def transferOpD (src dst : Reg) (hne : src ≠ dst := by decide) : OpD where
  prog := transferProg src (fun j => decide (j = dst))
  sem := fun s => Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)
  C := 4
  d := 1
  exec := fun s => ⟨_, by
    have h := stack_transfer src (fun j => decide (j = dst)) s
    have e : transferStore src (fun j => decide (j = dst)) s =
        Function.update (Function.update s src []) dst ((s src).reverse ++ s dst) := by
      funext j
      unfold transferStore
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne]
      · by_cases h2 : j = dst
        · subst h2; simp [Function.update_apply, h1]
        · simp [Function.update_apply, h1, h2]
    rw [e] at h; exact h, by have := len_lt_mu s src; simp; omega⟩
  grow := fun s => by
    have a1 := size_update s src []
    have a2 := size_update (Function.update s src []) dst ((s src).reverse ++ s dst)
    have : Function.update s src [] dst = s dst := Function.update_of_ne (Ne.symm hne) _ _
    rw [this] at a2
    have := one_le_mu s
    simp at *; unfold mu; omega

def transferOp (src dst : Reg) (hne : src ≠ dst := by decide) : Op := (transferOpD src dst hne).toOp

def copyOpD (src dst tmp : Reg) (h1 : src ≠ dst := by decide) (h2 : src ≠ tmp := by decide)
    (h3 : dst ≠ tmp := by decide) : OpD where
  prog := .seq (clearProg tmp) (copyProg src dst tmp)
  sem := fun s => Function.update (Function.update s tmp []) dst (s src ++ s dst)
  C := 14
  d := 1
  exec := fun s => ⟨_, by
    have c1 := (stack_basic_macros tmp s).2.2
    have c2 := stack_copy src dst tmp h1 h2 h3 (Function.update s tmp []) (by simp)
    have e1 : Function.update s tmp [] src = s src := Function.update_of_ne h2 _ _
    have e2 : Function.update s tmp [] dst = s dst := Function.update_of_ne h3 _ _
    rw [e1, e2] at c2
    exact StackProg.Exec.seq c1 c2, by
    have := len_lt_mu s src; have := len_lt_mu s tmp; simp; omega⟩
  grow := fun s => by
    have a1 := size_update s tmp []
    have a2 := size_update (Function.update s tmp []) dst (s src ++ s dst)
    have e2 : Function.update s tmp [] dst = s dst := Function.update_of_ne h3 _ _
    rw [e2] at a2
    have := len_le_size s src
    simp at *; unfold mu; omega

def copyOp (src dst tmp : Reg) (h1 : src ≠ dst := by decide) (h2 : src ≠ tmp := by decide)
    (h3 : dst ≠ tmp := by decide) : Op := (copyOpD src dst tmp h1 h2 h3).toOp

theorem length_flatten_replicate (n : ℕ) (l : List Bool) :
    (List.replicate n l).flatten.length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]; ring

def emb4 (a b c d : Reg) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d) : Fin 4 ↪ Reg :=
  ⟨![a, b, c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm]⟩

section
variable (a b c d : Reg) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d)
theorem emb4_0 : emb4 a b c d h1 h2 h3 h4 h5 h6 0 = a := rfl
theorem emb4_1 : emb4 a b c d h1 h2 h3 h4 h5 h6 1 = b := rfl
theorem emb4_2 : emb4 a b c d h1 h2 h3 h4 h5 h6 2 = c := rfl
theorem emb4_3 : emb4 a b c d h1 h2 h3 h4 h5 h6 3 = d := rfl
end

def repOpD (a dst cnt tc tz : Reg) (h1 : a ≠ dst := by decide) (h2 : a ≠ cnt := by decide)
    (h3 : a ≠ tc := by decide) (h4 : a ≠ tz := by decide) (h5 : dst ≠ cnt := by decide)
    (h6 : dst ≠ tc := by decide) (h7 : dst ≠ tz := by decide) (h8 : cnt ≠ tc := by decide)
    (h9 : cnt ≠ tz := by decide) (h10 : tc ≠ tz := by decide) : OpD where
  prog := .seq (clearProg tc) (.seq (.seq (clearProg tz) (copyProg cnt tc tz))
    (repeatCopyProg (emb4 a dst tc tz h1 h3 h4 h6 h7 h10)))
  sem := fun s => Function.update (Function.update (Function.update s tc []) tz []) dst
    ((List.replicate (s cnt).length (s a)).flatten ++ s dst)
  C := 30
  d := 2
  exec := fun s => by
    have c1 := (stack_basic_macros tc s).2.2
    set s1 := Function.update s tc [] with hs1
    have c2 := (stack_basic_macros tz s1).2.2
    set s2 := Function.update s1 tz [] with hs2
    have c3 := stack_copy cnt tc tz h8 h9 h10 s2 (by simp [hs2])
    set s3 := Function.update s2 tc (s2 cnt ++ s2 tc) with hs3
    have c4 := stack_repeat_copy (emb4 a dst tc tz h1 h3 h4 h6 h7 h10) s3
      (by rw [emb4_3]; simp [hs3, Function.update_apply, h10.symm, hs2])
    simp only [emb4_0, emb4_1, emb4_2] at c4
    have ex := StackProg.Exec.seq c1 (StackProg.Exec.seq (StackProg.Exec.seq c2 c3) c4)
    have v1 : s3 tc = s cnt := by simp [hs3, hs2, hs1, Function.update_apply, h8, h9]
    have v2 : s3 a = s a := by simp [hs3, hs2, hs1, Function.update_apply, h3, h4]
    have v3 : s3 dst = s dst := by simp [hs3, hs2, hs1, Function.update_apply, h6, h7]
    have v4 : s1 tz = s tz := by simp [hs1, Function.update_apply, h10.symm]
    have v5 : s2 cnt = s cnt := by simp [hs2, hs1, Function.update_apply, h8, h9]
    rw [v1, v2, v3, v4, v5] at ex
    have est : Function.update (Function.update s3 tc []) dst
        ((List.replicate (s cnt).length (s a)).flatten ++ s dst) =
        Function.update (Function.update (Function.update s tc []) tz []) dst
        ((List.replicate (s cnt).length (s a)).flatten ++ s dst) := by
      funext j
      simp only [hs3, hs2, hs1, Function.update_apply]
      split_ifs <;> simp_all
    rw [est] at ex
    refine ⟨_, ex, ?_⟩
    have := len_lt_mu s tc; have := len_lt_mu s tz; have := len_lt_mu s cnt
    have := len_lt_mu s a
    have hsq : (6 * (s a).length + 7) * (s cnt).length ≤ 7 * mu s ^ 2 := by nlinarith
    have : mu s ≤ mu s ^ 2 := by nlinarith
    nlinarith
  grow := fun s => by
    have a1 := size_update s tc []
    have a2 := size_update (Function.update s tc []) tz []
    have a3 := size_update (Function.update (Function.update s tc []) tz []) dst
      ((List.replicate (s cnt).length (s a)).flatten ++ s dst)
    have e : Function.update (Function.update s tc []) tz [] dst = s dst := by
      simp [Function.update_apply, h6, h7]
    rw [e] at a3
    rw [List.length_append, length_flatten_replicate] at a3
    have := len_lt_mu s cnt; have := len_lt_mu s a
    have : (s cnt).length * (s a).length ≤ mu s ^ 2 := by nlinarith
    simp at a1 a2
    unfold mu at *
    nlinarith

def repOp (a dst cnt tc tz : Reg) (h1 : a ≠ dst := by decide) (h2 : a ≠ cnt := by decide)
    (h3 : a ≠ tc := by decide) (h4 : a ≠ tz := by decide) (h5 : dst ≠ cnt := by decide)
    (h6 : dst ≠ tc := by decide) (h7 : dst ≠ tz := by decide) (h8 : cnt ≠ tc := by decide)
    (h9 : cnt ≠ tz := by decide) (h10 : tc ≠ tz := by decide) : Op :=
  (repOpD a dst cnt tc tz h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).toOp

/-! ### Loop operations -/

def lead : List Bool → ℕ
  | true :: l => lead l + 1
  | _ => 0

def rest : List Bool → List Bool
  | true :: l => rest l
  | l => l

theorem lead_add_rest (l : List Bool) : lead l + (rest l).length = l.length := by
  induction l with
  | nil => simp [lead, rest]
  | cons b l ih => cases b <;> simp [lead, rest]
                   omega

def toAct (src dst : Reg) : (Reg → Option Bool) → Reg → StackAct Bool :=
  fun _ j => if j = src then .pop else if j = dst then .push true else .keep

def toLoop (src dst : Reg) : StackProg Reg Bool :=
  .loop (fun h => decide (h src = some true)) (.act (toAct src dst))

theorem toLoop_exec (src dst : Reg) (hne : src ≠ dst) : ∀ (l : List Bool) (s : St), s src = l →
    (toLoop src dst).Exec s (Function.update (Function.update s src (rest l)) dst
      (List.replicate (lead l) true ++ s dst)) (3 * lead l + 1) := by
  intro l
  induction l with
  | nil =>
    intro s hs
    have e : Function.update (Function.update s src (rest [])) dst
        (List.replicate (lead []) true ++ s dst) = s := by
      funext j
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne, hs, rest]
      · by_cases h2 : j = dst
        · subst h2; simp [Function.update_apply, h1, lead]
        · simp [Function.update_apply, h1, h2]
    rw [e]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons b l ih =>
    intro s hs
    cases b with
    | false =>
      have e : Function.update (Function.update s src (rest (false :: l))) dst
          (List.replicate (lead (false :: l)) true ++ s dst) = s := by
        funext j
        by_cases h1 : j = src
        · subst h1; simp [Function.update_apply, hne, hs, rest]
        · by_cases h2 : j = dst
          · subst h2; simp [Function.update_apply, h1, lead]
          · simp [Function.update_apply, h1, h2]
      rw [e]
      exact StackProg.Exec.loopFalse (by simp [hs])
    | true =>
      have hact := StackProg.Exec.act (toAct src dst) s
      have e1 : StackProg.applyAct (toAct src dst) s =
          Function.update (Function.update s src l) dst (true :: s dst) := by
        funext j
        simp only [StackProg.applyAct, toAct]
        by_cases h1 : j = src
        · subst h1; simp [hs, StackAct.apply, Function.update_apply, hne]
        · by_cases h2 : j = dst
          · subst h2; simp [StackAct.apply, Function.update_apply, h1]
          · simp [StackAct.apply, Function.update_apply, h1, h2]
      rw [e1] at hact
      have hrec := ih (Function.update (Function.update s src l) dst (true :: s dst))
        (by simp [Function.update_apply, hne])
      have := StackProg.Exec.loopTrue (test := fun h => decide (h src = some true))
        (by simp [hs]) hact hrec
      have e2 : Function.update (Function.update
          (Function.update (Function.update s src l) dst (true :: s dst)) src (rest l)) dst
          (List.replicate (lead l) true ++
            Function.update (Function.update s src l) dst (true :: s dst) dst) =
          Function.update (Function.update s src (rest (true :: l))) dst
          (List.replicate (lead (true :: l)) true ++ s dst) := by
        funext j
        by_cases h1 : j = src
        · subst h1; simp [Function.update_apply, hne, rest]
        · by_cases h2 : j = dst
          · subst h2; simp [Function.update_apply, h1, lead, List.replicate_succ']
          · simp [Function.update_apply, h1, h2]
      rw [e2] at this
      have e3 : 1 + 1 + 1 + (3 * lead l + 1) = 3 * lead (true :: l) + 1 := by
        simp [lead]; ring
      rw [e3] at this
      exact this

def takeOnesOpD (src dst : Reg) (hne : src ≠ dst := by decide) : OpD where
  prog := .seq (toLoop src dst) (popProg src)
  sem := fun s => Function.update (Function.update s src (rest (s src)).tail) dst
    (List.replicate (lead (s src)) true ++ s dst)
  C := 6
  d := 1
  exec := fun s => by
    have h1 := toLoop_exec src dst hne (s src) s rfl
    have h2 := (stack_basic_macros src (Function.update (Function.update s src (rest (s src))) dst
      (List.replicate (lead (s src)) true ++ s dst))).2.1
    have := StackProg.Exec.seq h1 h2
    have e : Function.update (Function.update (Function.update s src (rest (s src))) dst
        (List.replicate (lead (s src)) true ++ s dst)) src
        (Function.update (Function.update s src (rest (s src))) dst
          (List.replicate (lead (s src)) true ++ s dst) src).tail =
        Function.update (Function.update s src (rest (s src)).tail) dst
          (List.replicate (lead (s src)) true ++ s dst) := by
      funext j
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne]
      · by_cases h2 : j = dst
        · subst h2; simp [Function.update_apply, h1, hne, Ne.symm hne]
        · simp [Function.update_apply, h1, h2]
    rw [e] at this
    refine ⟨_, this, ?_⟩
    have := lead_add_rest (s src)
    have := len_lt_mu s src
    simp; omega
  grow := fun s => by
    have a1 := size_update s src (rest (s src)).tail
    have a2 := size_update (Function.update s src (rest (s src)).tail) dst
      (List.replicate (lead (s src)) true ++ s dst)
    have e2 : Function.update s src (rest (s src)).tail dst = s dst :=
      Function.update_of_ne (Ne.symm hne) _ _
    rw [e2] at a2
    have := lead_add_rest (s src)
    have : (rest (s src)).tail.length ≤ (rest (s src)).length := by simp
    have := one_le_mu s
    simp only [List.length_append, List.length_replicate] at a2
    unfold mu at *; simp only [pow_one] at *; omega

def takeOnesOp (src dst : Reg) (hne : src ≠ dst := by decide) : Op := (takeOnesOpD src dst hne).toOp

def halveProg (src dst : Reg) : StackProg Reg Bool :=
  .loop (fun h => (h src).isSome) (.seq (popProg src)
    (.branch (fun h => (h src).isSome) (.seq (popProg src) (pushProg dst true)) skipProg))

theorem halve_exec (src dst : Reg) (hne : src ≠ dst) : ∀ (n : ℕ) (l : List Bool) (s : St),
    l.length = n → s src = l → ∃ c, c ≤ 7 * n + 1 ∧ (halveProg src dst).Exec s
      (Function.update (Function.update s src []) dst
        (List.replicate (n / 2) true ++ s dst)) c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l s hl hs
  match l, hl with
  | [], hl =>
    subst hl
    refine ⟨1, by omega, ?_⟩
    have e : Function.update (Function.update s src []) dst
        (List.replicate (([] : List Bool).length / 2) true ++ s dst) = s := by
      funext j
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne, hs]
      · by_cases h2 : j = dst
        · subst h2; simp [Function.update_apply, h1]
        · simp [Function.update_apply, h1, h2]
    rw [e]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | [b], hl =>
    subst hl
    refine ⟨7, by simp, ?_⟩
    have c1 := (stack_basic_macros src s).2.1
    rw [hs] at c1
    simp only [List.tail_cons] at c1
    have c2 : (StackProg.branch (fun h => (h src).isSome) (.seq (popProg src) (pushProg dst true))
        skipProg).Exec (Function.update s src []) (Function.update s src []) (1 + 1) :=
      StackProg.Exec.branchFalse (by simp) (skip_exec _)
    have c3 := StackProg.Exec.seq c1 c2
    have c4 : (halveProg src dst).Exec (Function.update s src []) (Function.update s src []) 1 :=
      StackProg.Exec.loopFalse (by simp)
    have := StackProg.Exec.loopTrue (test := fun h => (h src).isSome) (by simp [hs]) c3 c4
    have e : Function.update s src [] = Function.update (Function.update s src []) dst
        (List.replicate ([b].length / 2) true ++ s dst) := by
      funext j
      by_cases h2 : j = dst
      · subst h2; simp [Function.update_apply, Ne.symm hne]
      · simp [Function.update_apply, h2]
    rw [e] at this
    exact this
  | b :: c :: l', hl =>
    have hn : n = l'.length + 2 := by simp at hl; omega
    have c1 := (stack_basic_macros src s).2.1
    rw [hs] at c1
    simp only [List.tail_cons] at c1
    set s1 := Function.update s src (c :: l') with hs1
    have c2 := (stack_basic_macros src s1).2.1
    have e1 : s1 src = c :: l' := by simp [hs1]
    rw [e1] at c2
    simp only [List.tail_cons] at c2
    set s2 := Function.update s1 src l' with hs2
    have c3 := (stack_basic_macros dst s2).1 true
    set s3 := Function.update s2 dst (true :: s2 dst) with hs3
    have c4 : (StackProg.branch (fun h => (h src).isSome) (.seq (popProg src) (pushProg dst true))
        skipProg).Exec s1 s3 (1 + (1 + 1 + 1)) :=
      StackProg.Exec.branchTrue (by simp [e1]) (StackProg.Exec.seq c2 c3)
    have c5 := StackProg.Exec.seq c1 c4
    obtain ⟨c', hc', c6⟩ := ih l'.length (by omega) l' s3 rfl
      (by simp [hs3, hs2, Function.update_apply, hne])
    have := StackProg.Exec.loopTrue (test := fun h => (h src).isSome) (by simp [hs]) c5 c6
    have e : Function.update (Function.update s3 src []) dst
        (List.replicate (l'.length / 2) true ++ s3 dst) =
        Function.update (Function.update s src []) dst (List.replicate (n / 2) true ++ s dst) := by
      have hn2 : n / 2 = l'.length / 2 + 1 := by omega
      funext j
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne]
      · by_cases h2 : j = dst
        · subst h2
          simp [hs3, hs2, hs1, Function.update_apply, h1, hn2, List.replicate_succ', Ne.symm hne]
        · simp [hs3, hs2, hs1, Function.update_apply, h1, h2]
    rw [e] at this
    exact ⟨_, by omega, this⟩

def halveOpD (src dst : Reg) (hne : src ≠ dst := by decide) : OpD where
  prog := halveProg src dst
  sem := fun s => Function.update (Function.update s src []) dst
    (List.replicate ((s src).length / 2) true ++ s dst)
  C := 8
  d := 1
  exec := fun s => by
    obtain ⟨c, hc, h⟩ := halve_exec src dst hne (s src).length (s src) s rfl rfl
    refine ⟨c, h, ?_⟩
    have := len_lt_mu s src
    simp; omega
  grow := fun s => by
    have a1 := size_update s src []
    have a2 := size_update (Function.update s src []) dst
      (List.replicate ((s src).length / 2) true ++ s dst)
    have e2 : Function.update s src [] dst = s dst := Function.update_of_ne (Ne.symm hne) _ _
    rw [e2] at a2
    have := one_le_mu s
    have : (s src).length / 2 ≤ (s src).length := Nat.div_le_self _ _
    simp only [List.length_append, List.length_replicate, List.length_nil] at a1 a2
    unfold mu at *; simp only [pow_one] at *; omega

def halveOp (src dst : Reg) (hne : src ≠ dst := by decide) : Op := (halveOpD src dst hne).toOp

def bitChunk (c0 c1 : List Bool) (b : Bool) : List Bool := if b then c1 else c0

def expandBody (src dst : Reg) (c0 c1 : List Bool) : StackProg Reg Bool :=
  .branch (fun h => decide (h src = some true))
    (.seq (popProg src) (pushRevProg dst c1)) (.seq (popProg src) (pushRevProg dst c0))

def expandProg (src dst : Reg) (c0 c1 : List Bool) : StackProg Reg Bool :=
  .loop (fun h => (h src).isSome) (expandBody src dst c0 c1)

theorem expandBody_exec (src dst : Reg) (hne : src ≠ dst) (c0 c1 : List Bool) (b : Bool)
    (l : List Bool) (s : St) (hs : s src = b :: l) :
    (expandBody src dst c0 c1).Exec s (Function.update (Function.update s src l) dst
      ((bitChunk c0 c1 b).reverse ++ s dst)) (1 + (1 + 1 + (2 * (bitChunk c0 c1 b).length + 1))) := by
  have p1 := (stack_basic_macros src s).2.1
  rw [hs] at p1
  simp only [List.tail_cons] at p1
  have p2 := pushRev_exec dst (bitChunk c0 c1 b) (Function.update s src l)
  have e : Function.update s src l dst = s dst := Function.update_of_ne (Ne.symm hne) _ _
  rw [e] at p2
  cases b with
  | true =>
    exact StackProg.Exec.branchTrue (by simp [hs]) (StackProg.Exec.seq p1 p2)
  | false =>
    exact StackProg.Exec.branchFalse (by simp [hs]) (StackProg.Exec.seq p1 p2)

theorem bitChunk_len_le (c0 c1 : List Bool) (b : Bool) :
    (bitChunk c0 c1 b).length ≤ c0.length + c1.length := by
  cases b <;> simp [bitChunk]

theorem expand_exec (src dst : Reg) (hne : src ≠ dst) (c0 c1 : List Bool) :
    ∀ (l : List Bool) (s : St), s src = l → ∃ c,
      c ≤ (2 * (c0.length + c1.length) + 6) * l.length + 1 ∧
      (expandProg src dst c0 c1).Exec s (Function.update (Function.update s src []) dst
        ((l.flatMap (bitChunk c0 c1)).reverse ++ s dst)) c := by
  intro l
  induction l with
  | nil =>
    intro s hs
    refine ⟨1, by simp, ?_⟩
    have e : Function.update (Function.update s src []) dst
        ((([] : List Bool).flatMap (bitChunk c0 c1)).reverse ++ s dst) = s := by
      funext j
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne, hs]
      · by_cases h2 : j = dst
        · subst h2; simp [Function.update_apply, h1]
        · simp [Function.update_apply, h1, h2]
    rw [e]
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons b l ih =>
    intro s hs
    have hb := expandBody_exec src dst hne c0 c1 b l s hs
    obtain ⟨c', hc', hr⟩ := ih (Function.update (Function.update s src l) dst
      ((bitChunk c0 c1 b).reverse ++ s dst)) (by simp [Function.update_apply, hne])
    have := StackProg.Exec.loopTrue (test := fun h => (h src).isSome) (by simp [hs]) hb hr
    have e : Function.update (Function.update (Function.update (Function.update s src l) dst
        ((bitChunk c0 c1 b).reverse ++ s dst)) src []) dst
        ((l.flatMap (bitChunk c0 c1)).reverse ++ Function.update (Function.update s src l) dst
          ((bitChunk c0 c1 b).reverse ++ s dst) dst) =
        Function.update (Function.update s src []) dst
          (((b :: l).flatMap (bitChunk c0 c1)).reverse ++ s dst) := by
      funext j
      by_cases h1 : j = src
      · subst h1; simp [Function.update_apply, hne]
      · by_cases h2 : j = dst
        · subst h2; simp [Function.update_apply, h1]
        · simp [Function.update_apply, h1, h2]
    rw [e] at this
    refine ⟨_, ?_, this⟩
    have := bitChunk_len_le c0 c1 b
    simp only [List.length_cons]
    nlinarith

theorem flatMap_bitChunk_len (c0 c1 l : List Bool) :
    (l.flatMap (bitChunk c0 c1)).length ≤ l.length * (c0.length + c1.length) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have := bitChunk_len_le c0 c1 b
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

def expandOpD (src dst : Reg) (c0 c1 : List Bool) (hne : src ≠ dst := by decide) : OpD where
  prog := expandProg src dst c0 c1
  sem := fun s => Function.update (Function.update s src []) dst
    (((s src).flatMap (bitChunk c0 c1)).reverse ++ s dst)
  C := 2 * (c0.length + c1.length) + 9
  d := 1
  exec := fun s => by
    obtain ⟨c, hc, h⟩ := expand_exec src dst hne c0 c1 (s src) s rfl
    refine ⟨c, h, ?_⟩
    have := len_lt_mu s src
    simp; nlinarith
  grow := fun s => by
    have a1 := size_update s src []
    have a2 := size_update (Function.update s src [])  dst
      (((s src).flatMap (bitChunk c0 c1)).reverse ++ s dst)
    have e2 : Function.update s src [] dst = s dst := Function.update_of_ne (Ne.symm hne) _ _
    rw [e2] at a2
    have := flatMap_bitChunk_len c0 c1 (s src)
    have := len_lt_mu s src
    simp only [List.length_append, List.length_reverse, List.length_nil] at a1 a2
    unfold mu at *; simp only [pow_one] at *; nlinarith

def expandOp (src dst : Reg) (c0 c1 : List Bool) (hne : src ≠ dst := by decide) : Op := (expandOpD src dst c0 c1 hne).toOp

/-! ### Polynomial time of an operation -/

def initSt (w : List Bool) : St := fun j => if j = Reg.inp then w else []

theorem size_init (w : List Bool) : size (initSt w) = w.length := by
  unfold size initSt
  simp [apply_ite List.length]

theorem op_polytime (o : Op) : PolyTimeComputable (fun w => o.sem (initSt w) Reg.out) := by
  obtain ⟨C, d, ex, _⟩ := o.poly
  obtain ⟨k, hk⟩ := polynomial_absorb C d 0
  refine stack_program_polytime o.prog Reg.inp Reg.out _ k (fun w => ?_)
  obtain ⟨n, hn, hb⟩ := ex (initSt w)
  refine ⟨o.sem (initSt w), n, ?_, hn, rfl⟩
  have := hk w.length
  have hm : mu (initSt w) = w.length + 1 := by unfold mu; rw [size_init]
  rw [hm] at hb; omega

/-! ### Semantic equations of the operations -/

section sems
variable (s : St)
theorem copyOp_sem (a b c : Reg) (h1 h2 h3) :
    (copyOp a b c h1 h2 h3).sem s = Function.update (Function.update s c []) b (s a ++ s b) := rfl
theorem repOp_sem (a dst cnt tc tz : Reg) (h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) :
    (repOp a dst cnt tc tz h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).sem s =
      Function.update (Function.update (Function.update s tc []) tz []) dst
        ((List.replicate (s cnt).length (s a)).flatten ++ s dst) := rfl
theorem pushListOp_sem (k : Reg) (l : List Bool) :
    (pushListOp k l).sem s = Function.update s k (l ++ s k) := rfl
theorem pushOp_sem (k : Reg) (b : Bool) :
    (pushOp k b).sem s = Function.update s k (b :: s k) := rfl
theorem popOp_sem (k : Reg) : (popOp k).sem s = Function.update s k (s k).tail := rfl
theorem clearOp_sem (k : Reg) : (clearOp k).sem s = Function.update s k [] := rfl
theorem transferOp_sem (a b : Reg) (h) : (transferOp a b h).sem s =
    Function.update (Function.update s a []) b ((s a).reverse ++ s b) := rfl
theorem halveOp_sem (a b : Reg) (h) : (halveOp a b h).sem s =
    Function.update (Function.update s a []) b (List.replicate ((s a).length / 2) true ++ s b) := rfl
theorem takeOnesOp_sem (a b : Reg) (h) : (takeOnesOp a b h).sem s =
    Function.update (Function.update s a (rest (s a)).tail) b
      (List.replicate (lead (s a)) true ++ s b) := rfl
theorem expandOp_sem (a b : Reg) (c0 c1 : List Bool) (h) : (expandOp a b c0 c1 h).sem s =
    Function.update (Function.update s a []) b (((s a).flatMap (bitChunk c0 c1)).reverse ++ s b) :=
  rfl
theorem seq_sem (o1 o2 : Op) : (o1.seq o2).sem s = o2.sem (o1.sem s) := rfl
theorem skip_sem : Op.skip.sem s = s := rfl
end sems

theorem flat_rep_rep (n m : ℕ) (b : Bool) :
    (List.replicate n (List.replicate m b)).flatten = List.replicate (n * m) b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_append_replicate]
    congr 1; ring

theorem lead_rep (n : ℕ) (l : List Bool) : lead (List.replicate n true ++ false :: l) = n := by
  induction n with
  | zero => simp [lead]
  | succ n ih => simp [List.replicate_succ, lead, ih]

theorem rest_rep (n : ℕ) (l : List Bool) :
    rest (List.replicate n true ++ false :: l) = false :: l := by
  induction n with
  | zero => simp [rest]
  | succ n ih => simp [List.replicate_succ, rest, ih]

/-! ### The program -/

def cI : List Bool := [true, true, true, true, true, false]
def cRG : List Bool := [true, true, false]
def preB : List Bool := [true, true, true, true, true, false, true, false, false]
def cfB : List Bool := [true, false, true, true, true, false, true, false, true, false, false]
def h0B : List Bool := [false, false] ++ preB
def ttB : List Bool := [true, true, false, true, true, true, true]
def c6O : List Bool := [false, false, false, true, true, true]
def c6Z : List Bool := [false, false, false, false, false, true]
def c6A : List Bool := [true, true, false, true, true, true]

def numOps1 (staging : ℕ) : List Op :=
  [takeOnesOp .inp .s, takeOnesOp .inp .t,
   copyOp .t .ta .tz, halveOp .ta .th, repOp .s .st .t .tc .tz] ++
  List.replicate 16 (copyOp .s .bp .tz) ++ List.replicate 5 (copyOp .st .bp .tz) ++
  [pushListOp .bp (List.replicate 6 true), copyOp .t .bp .tz, copyOp .th .bp .tz] ++
  List.replicate 6 (copyOp .t .bbh .tz) ++ [pushListOp .bbh (List.replicate (22 + staging) true)] ++
  List.replicate 3 (copyOp .s .bbh .tz) ++
  List.replicate 2 (copyOp .bbh .nb .tz) ++ List.replicate 4 (copyOp .bp .nb .tz) ++
  [pushListOp .nb (List.replicate 8 true), copyOp .bp .pf .tz] ++
  List.replicate 6 (copyOp .s .pf .tz) ++
  [pushListOp .pf (List.replicate 7 true), repOp .nb .b .pf .tc .tz, pushListOp .b [true],
   pushListOp .x [true]]

def bPv (s t : ℕ) : ℕ := 16 * s + 5 * (t * s) + 6 + t + t / 2
def bbhv (staging s t : ℕ) : ℕ := 6 * t + 22 + staging + 3 * s
def nbv (staging s t : ℕ) : ℕ := 2 * bbhv staging s t + 4 * bPv s t + 8
def pfv (s t : ℕ) : ℕ := bPv s t + 6 * s + 7
def Bv (staging s t : ℕ) : ℕ := nbv staging s t * pfv s t + 1

def sA (E : List Bool) (staging s t : ℕ) : St := fun j => match j with
  | .inp => E
  | .s => List.replicate s true
  | .t => List.replicate t true
  | .th => List.replicate (t / 2) true
  | .st => List.replicate (t * s) true
  | .bp => List.replicate (bPv s t) true
  | .bbh => List.replicate (bbhv staging s t) true
  | .nb => List.replicate (nbv staging s t) true
  | .pf => List.replicate (pfv s t) true
  | .b => List.replicate (Bv staging s t) true
  | .x => [true]
  | _ => []


/-! ### Helper lemmas for `opList` and single-step execution (linear AST size) -/

theorem opList_append (l1 l2 : List Op) (s : St) :
    (opList (l1 ++ l2)).sem s = (opList l2).sem ((opList l1).sem s) := by
  induction l1 generalizing s with
  | nil => rfl
  | cons o l1 ih => simp only [List.cons_append, opList_cons_sem, ih]

theorem opList_repCopy (n : ℕ) (src dst tmp : Reg) (h1 h2 h3) (s : St) (ht : s tmp = []) :
    (opList (List.replicate n (copyOp src dst tmp h1 h2 h3))).sem s =
      Function.update s dst ((List.replicate n (s src)).flatten ++ s dst) := by
  induction n generalizing s with
  | zero => simp [opList_nil_sem]
  | succ n ih =>
    rw [List.replicate_succ, opList_cons_sem, copyOp_sem]
    have htm : Function.update s tmp [] = s := Function.update_eq_self_iff.mpr ht.symm
    rw [htm, ih _ (by simp [Function.update_apply, h3.symm, ht])]
    funext j
    by_cases hj : j = dst
    · subst hj; simp [Function.update_apply, h1, List.replicate_succ']
    · simp [Function.update_apply, hj]

theorem opList_repPop (n : ℕ) (k : Reg) (s : St) :
    (opList (List.replicate n (popOp k))).sem s = Function.update s k ((s k).drop n) := by
  induction n generalizing s with
  | zero => simp [opList_nil_sem]
  | succ n ih =>
    rw [List.replicate_succ, opList_cons_sem, popOp_sem, ih]
    funext j
    by_cases hj : j = k
    · subst hj
      simp only [Function.update_self]
      cases s j <;> simp
    · simp [Function.update_apply, hj]

theorem getElem_flatten_replicate {α : Type*} (n : ℕ) (c : List α) (hc : 0 < c.length)
    (i : ℕ) (hi : i < (List.replicate n c).flatten.length) :
    (List.replicate n c).flatten[i] = c.get ⟨i % c.length, Nat.mod_lt i hc⟩ := by
  induction n generalizing i with
  | zero => simp at hi
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    by_cases hlt : i < c.length
    · rw [List.getElem_append_left hlt]
      simp [Nat.mod_eq_of_lt hlt]
    · rw [List.getElem_append_right (by omega)]
      rw [ih (i - c.length) (by simp only [List.replicate_succ, List.flatten_cons,
        List.length_append] at hi; omega)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      have hsub : i - c.length + c.length = i := by omega
      have hmod : (i - c.length) % c.length = (i - c.length + c.length) % c.length :=
        (Nat.add_mod_right _ _).symm
      rw [hmod, hsub]

section run_lemmas
theorem run_push {k : Reg} {b : Bool} {v : List Bool} {os : List Op} {s : St} (hk : s k = v) :
    (opList (pushOp k b :: os)).sem s = (opList os).sem (Function.update s k (b :: v)) := by
  rw [opList_cons_sem, pushOp_sem, hk]

theorem run_pushList {k : Reg} {l v : List Bool} {os : List Op} {s : St} (hk : s k = v) :
    (opList (pushListOp k l :: os)).sem s = (opList os).sem (Function.update s k (l ++ v)) := by
  rw [opList_cons_sem, pushListOp_sem, hk]

theorem run_clear {k : Reg} {os : List Op} {s : St} :
    (opList (clearOp k :: os)).sem s = (opList os).sem (Function.update s k []) := rfl

theorem run_copy {src dst tmp : Reg} {h1 h2 h3} {a b : List Bool} {os : List Op} {s : St}
    (ha : s src = a) (hb : s dst = b) (ht : s tmp = []) :
    (opList (copyOp src dst tmp h1 h2 h3 :: os)).sem s =
      (opList os).sem (Function.update s dst (a ++ b)) := by
  rw [opList_cons_sem, copyOp_sem, ha, hb]
  have htm : Function.update s tmp [] = s := Function.update_eq_self_iff.mpr ht.symm
  rw [htm]

theorem run_repCopy {n : ℕ} {src dst tmp : Reg} {h1 h2 h3} {a b : List Bool} {os : List Op} {s : St}
    (ha : s src = a) (hb : s dst = b) (ht : s tmp = []) :
    (opList (List.replicate n (copyOp src dst tmp h1 h2 h3) ++ os)).sem s =
      (opList os).sem (Function.update s dst ((List.replicate n a).flatten ++ b)) := by
  rw [opList_append, opList_repCopy _ _ _ _ _ _ _ _ ht, ha, hb]

theorem run_rep {a dst cnt tc tz : Reg} {h1 h2 h3 h4 h5 h6 h7 h8 h9 h10}
    {va vd vc : List Bool} {os : List Op} {s : St}
    (ha : s a = va) (hd : s dst = vd) (hc : s cnt = vc)
    (htc : s tc = []) (htz : s tz = []) :
    (opList (repOp a dst cnt tc tz h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 :: os)).sem s =
      (opList os).sem (Function.update s dst ((List.replicate vc.length va).flatten ++ vd)) := by
  rw [opList_cons_sem, repOp_sem, ha, hd, hc]
  have htc' : Function.update s tc [] = s := Function.update_eq_self_iff.mpr htc.symm
  have htz' : Function.update s tz [] = s := Function.update_eq_self_iff.mpr htz.symm
  rw [htc', htz']

theorem run_transfer {src dst : Reg} {h} {a b : List Bool} {os : List Op} {s : St}
    (ha : s src = a) (hb : s dst = b) :
    (opList (transferOp src dst h :: os)).sem s =
      (opList os).sem (Function.update (Function.update s src []) dst (a.reverse ++ b)) := by
  rw [opList_cons_sem, transferOp_sem, ha, hb]

theorem run_halve {src dst : Reg} {h} {a b : List Bool} {os : List Op} {s : St}
    (ha : s src = a) (hb : s dst = b) :
    (opList (halveOp src dst h :: os)).sem s =
      (opList os).sem (Function.update (Function.update s src []) dst
        (List.replicate (a.length / 2) true ++ b)) := by
  rw [opList_cons_sem, halveOp_sem, ha, hb]

theorem run_takeOnes {src dst : Reg} {h} {n : ℕ} {restL b : List Bool} {os : List Op} {s : St}
    (ha : s src = List.replicate n true ++ false :: restL) (hb : s dst = b) :
    (opList (takeOnesOp src dst h :: os)).sem s =
      (opList os).sem (Function.update (Function.update s src restL) dst
        (List.replicate n true ++ b)) := by
  rw [opList_cons_sem, takeOnesOp_sem, ha, hb, lead_rep, rest_rep]; rfl

theorem run_expand {src dst : Reg} {h} {c0 c1 a b : List Bool} {os : List Op} {s : St}
    (ha : s src = a) (hb : s dst = b) :
    (opList (expandOp src dst c0 c1 h :: os)).sem s =
      (opList os).sem (Function.update (Function.update s src []) dst
        ((a.flatMap (bitChunk c0 c1)).reverse ++ b)) := by
  rw [opList_cons_sem, expandOp_sem, ha, hb]

theorem run_repPop {n : ℕ} {k : Reg} {a : List Bool} {os : List Op} {s : St} (ha : s k = a) :
    (opList (List.replicate n (popOp k) ++ os)).sem s =
      (opList os).sem (Function.update s k (a.drop n)) := by
  rw [opList_append, opList_repPop, ha]

theorem upd_idem {s : St} {k : Reg} {v1 v2 : List Bool} :
    Function.update (Function.update s k v1) k v2 = Function.update s k v2 := by
  funext j; by_cases h : j = k <;> simp [Function.update_apply, h]

theorem rep_true_add (a b : ℕ) :
    List.replicate a true ++ List.replicate b true = List.replicate (a + b) true :=
  List.replicate_append_replicate
end run_lemmas

/-! ### Phase 1 semantics: `numOps1` -/

theorem numOps1_sem (E : List Bool) (staging s t : ℕ) :
    (opList (numOps1 staging)).sem
      (initSt (List.replicate s true ++ false :: (List.replicate t true ++ false :: E))) =
      sA E staging s t := by
  unfold numOps1
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [run_takeOnes (n := s) (restL := List.replicate t true ++ false :: E) (b := [])
    (by simp [initSt]) (by simp [initSt])]
  simp only [List.append_nil]
  rw [run_takeOnes (n := t) (restL := E) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])]
  simp only [List.append_nil]
  rw [run_copy (a := List.replicate t true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [List.append_nil]
  rw [run_halve (a := List.replicate t true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])]
  simp only [List.length_replicate, List.append_nil]
  rw [run_rep (va := List.replicate s true) (vd := []) (vc := List.replicate t true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [List.length_replicate, flat_rep_rep, List.append_nil]
  rw [run_repCopy (a := List.replicate s true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_repCopy (a := List.replicate (t * s) true) (b := List.replicate (16 * s) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, initSt])]
  rw [flat_rep_rep, rep_true_add, upd_idem]
  rw [run_pushList (v := List.replicate (5 * (t * s) + 16 * s) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem]
  rw [run_copy (a := List.replicate t true) (b := List.replicate (6 + (5 * (t * s) + 16 * s)) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, initSt])]
  rw [rep_true_add, upd_idem]
  rw [run_copy (a := List.replicate (t / 2) true)
    (b := List.replicate (t + (6 + (5 * (t * s) + 16 * s))) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, initSt])]
  rw [rep_true_add, upd_idem]
  have hbp : t / 2 + (t + (6 + (5 * (t * s) + 16 * s))) = bPv s t := by unfold bPv; ring
  rw [hbp]
  rw [run_repCopy (a := List.replicate t true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_pushList (v := List.replicate (6 * t) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem]
  rw [run_repCopy (a := List.replicate s true) (b := List.replicate (22 + staging + 6 * t) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, initSt])]
  rw [flat_rep_rep, rep_true_add, upd_idem]
  have hbbh : 3 * s + (22 + staging + 6 * t) = bbhv staging s t := by unfold bbhv; ring
  rw [hbbh]
  rw [run_repCopy (a := List.replicate (bbhv staging s t) true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_repCopy (a := List.replicate (bPv s t) true)
    (b := List.replicate (2 * bbhv staging s t) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, initSt])]
  rw [flat_rep_rep, rep_true_add, upd_idem]
  rw [run_pushList (v := List.replicate (4 * bPv s t + 2 * bbhv staging s t) true)
    (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem]
  have hnb : 8 + (4 * bPv s t + 2 * bbhv staging s t) = nbv staging s t := by unfold nbv; ring
  rw [hnb]
  rw [run_copy (a := List.replicate (bPv s t) true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [List.append_nil]
  rw [run_repCopy (a := List.replicate s true) (b := List.replicate (bPv s t) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, initSt])]
  rw [flat_rep_rep, rep_true_add, upd_idem]
  rw [run_pushList (v := List.replicate (6 * s + bPv s t) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem]
  have hpf : 7 + (6 * s + bPv s t) = pfv s t := by unfold pfv; ring
  rw [hpf]
  rw [run_rep (va := List.replicate (nbv staging s t) true) (vd := [])
    (vc := List.replicate (pfv s t) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, initSt])
    (by simp [Function.update_apply, initSt])]
  simp only [List.length_replicate, flat_rep_rep, List.append_nil]
  rw [run_pushList (v := List.replicate (pfv s t * nbv staging s t) true)
    (by simp [Function.update_apply])]
  rw [show [true] = List.replicate 1 true from rfl, rep_true_add, upd_idem]
  have hb : 1 + pfv s t * nbv staging s t = Bv staging s t := by unfold Bv; ring
  rw [hb]
  rw [run_pushList (v := []) (by simp [Function.update_apply, initSt])]
  simp only [List.append_nil, opList_nil_sem]
  funext j; cases j <;> simp [Function.update_apply, initSt, sA]

/-! ### Phase 2: `powOps` -/

def powStep : List Op :=
  [repOp .b .y .x .tc .tz, clearOp .x, transferOp .y .x]

def powOps : ℕ → List Op
  | 0 => []
  | k + 1 => powStep ++ powOps k

def sAx (E : List Bool) (staging s t m : ℕ) : St := fun j => match j with
  | .inp => E
  | .s => List.replicate s true
  | .t => List.replicate t true
  | .th => List.replicate (t / 2) true
  | .st => List.replicate (t * s) true
  | .bp => List.replicate (bPv s t) true
  | .bbh => List.replicate (bbhv staging s t) true
  | .nb => List.replicate (nbv staging s t) true
  | .pf => List.replicate (pfv s t) true
  | .b => List.replicate (Bv staging s t) true
  | .x => List.replicate m true
  | _ => []

theorem sAx_one (E : List Bool) (staging s t : ℕ) : sAx E staging s t 1 = sA E staging s t := by
  funext j; cases j <;> rfl

theorem powStep_sem (E : List Bool) (staging s t m : ℕ) :
    (opList powStep).sem (sAx E staging s t m) =
      sAx E staging s t (m * Bv staging s t) := by
  unfold powStep
  rw [run_rep (va := List.replicate (Bv staging s t) true) (vd := []) (vc := List.replicate m true)
    rfl rfl rfl rfl rfl]
  simp only [List.length_replicate, flat_rep_rep, List.append_nil]
  rw [run_clear]
  rw [run_transfer (a := List.replicate (m * Bv staging s t) true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply])]
  simp only [List.reverse_replicate, List.append_nil, opList_nil_sem]
  funext j; cases j <;> simp [Function.update_apply, sAx]

theorem powOps_sem (E : List Bool) (staging s t : ℕ) :
    ∀ k m : ℕ, (opList (powOps k)).sem (sAx E staging s t m) =
      sAx E staging s t (m * Bv staging s t ^ k) := by
  intro k
  induction k with
  | zero => intro m; simp [powOps, opList_nil_sem]
  | succ k ih =>
    intro m
    rw [powOps, opList_append, powStep_sem, ih]
    congr 1; ring

/-! ### Phase 3: `numOps2` -/

def numOps2 (staging : ℕ) : List Op :=
  List.replicate 2 (copyOp .x .r .tz) ++
  [copyOp .bbh .h .tz, pushListOp .h (List.replicate 2 true), copyOp .r .h .tz] ++
  List.replicate 6 (copyOp .s .w6 .tz) ++ [pushListOp .w6 (List.replicate 6 true),
   copyOp .w6 .w .tz, pushOp .w true] ++
  List.replicate 6 (copyOp .s .w4 .tz) ++ [pushListOp .w4 (List.replicate 4 true)] ++
  List.replicate 3 (copyOp .s .s3 .tz) ++ [pushListOp .s3 (List.replicate 3 true),
   repOp .s3 .sq .x .tc .tz,
   copyOp .bp .ic .tz, pushOp .ic true, copyOp .sq .ic .tz,
   copyOp .t .l .tz, copyOp .th .l .tz, pushListOp .l (List.replicate 5 true)] ++
  List.replicate 3 (copyOp .s .ss .tz) ++ [pushListOp .ss (List.replicate staging true),
   copyOp .t .t2 .tz, pushListOp .t2 (List.replicate 2 true)]

def sC (E : List Bool) (staging s t x : ℕ) : St := fun j => match j with
  | .inp => E
  | .s => List.replicate s true
  | .t => List.replicate t true
  | .th => List.replicate (t / 2) true
  | .st => List.replicate (t * s) true
  | .bp => List.replicate (bPv s t) true
  | .bbh => List.replicate (bbhv staging s t) true
  | .nb => List.replicate (nbv staging s t) true
  | .pf => List.replicate (pfv s t) true
  | .b => List.replicate (Bv staging s t) true
  | .x => List.replicate x true
  | .r => List.replicate (2 * x) true
  | .h => List.replicate (bbhv staging s t + 2 + 2 * x) true
  | .w6 => List.replicate (6 * s + 6) true
  | .w => List.replicate (6 * s + 7) true
  | .w4 => List.replicate (6 * s + 4) true
  | .s3 => List.replicate (3 * s + 3) true
  | .sq => List.replicate (x * (3 * s + 3)) true
  | .ic => List.replicate (bPv s t + 1 + x * (3 * s + 3)) true
  | .l => List.replicate (t + t / 2 + 5) true
  | .ss => List.replicate (3 * s + staging) true
  | .t2 => List.replicate (t + 2) true
  | _ => []

theorem numOps2_sem (E : List Bool) (staging s t x : ℕ) :
    (opList (numOps2 staging)).sem (sAx E staging s t x) = sC E staging s t x := by
  unfold numOps2
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [run_repCopy (a := List.replicate x true) (b := []) rfl rfl rfl]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_copy (a := List.replicate (bbhv staging s t) true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [List.append_nil]
  rw [run_pushList (v := List.replicate (bbhv staging s t) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem]
  rw [run_copy (a := List.replicate (2 * x) true) (b := List.replicate (2 + bbhv staging s t) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sAx])]
  rw [rep_true_add, upd_idem]
  have hh : 2 * x + (2 + bbhv staging s t) = bbhv staging s t + 2 + 2 * x := by ring
  rw [hh]
  rw [run_repCopy (a := List.replicate s true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_pushList (v := List.replicate (6 * s) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem, show 6 + 6 * s = 6 * s + 6 by ring]
  rw [run_copy (a := List.replicate (6 * s + 6) true) (b := [])
    (by simp [Function.update_apply]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [List.append_nil]
  rw [run_push (v := List.replicate (6 * s + 6) true) (by simp [Function.update_apply])]
  rw [← List.replicate_succ, upd_idem]
  rw [run_repCopy (a := List.replicate s true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_pushList (v := List.replicate (6 * s) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem, show 4 + 6 * s = 6 * s + 4 by ring]
  rw [run_repCopy (a := List.replicate s true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_pushList (v := List.replicate (3 * s) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem, show 3 + 3 * s = 3 * s + 3 by ring]
  rw [run_rep (va := List.replicate (3 * s + 3) true) (vd := []) (vc := List.replicate x true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [List.length_replicate, flat_rep_rep, List.append_nil]
  rw [run_copy (a := List.replicate (bPv s t) true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [List.append_nil]
  rw [run_push (v := List.replicate (bPv s t) true) (by simp [Function.update_apply])]
  rw [← List.replicate_succ, upd_idem]
  rw [run_copy (a := List.replicate (x * (3 * s + 3)) true) (b := List.replicate (bPv s t + 1) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sAx])]
  rw [rep_true_add, upd_idem, show x * (3 * s + 3) + (bPv s t + 1) = bPv s t + 1 + x * (3 * s + 3) by ring]
  rw [run_copy (a := List.replicate t true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [List.append_nil]
  rw [run_copy (a := List.replicate (t / 2) true) (b := List.replicate t true)
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sAx])]
  rw [rep_true_add, upd_idem]
  rw [run_pushList (v := List.replicate (t / 2 + t) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem, show 5 + (t / 2 + t) = t + t / 2 + 5 by ring]
  rw [run_repCopy (a := List.replicate s true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [flat_rep_rep, List.append_nil]
  rw [run_pushList (v := List.replicate (3 * s) true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem, show staging + 3 * s = 3 * s + staging by ring]
  rw [run_copy (a := List.replicate t true) (b := [])
    (by simp [Function.update_apply, sAx]) (by simp [Function.update_apply, sAx])
    (by simp [Function.update_apply, sAx])]
  simp only [List.append_nil]
  rw [run_pushList (v := List.replicate t true) (by simp [Function.update_apply])]
  rw [rep_true_add, upd_idem, show 2 + t = t + 2 by ring, opList_nil_sem]
  funext j; cases j <;> simp [Function.update_apply, sAx, sC]

/-! ### Phase 4: `piecesOps` -/

def piecesOps : List Op :=
  [pushOp .buf false, repOp .buf .out .sq .tc .tz, clearOp .buf,
   pushListOp .out cRG,
   pushListOp .buf cI, repOp .buf .out .l .tc .tz,
   pushListOp .out cRG,
   repOp .buf .out .s .tc .tz, clearOp .buf,
   expandOp .inp .buf h0B cfB] ++
  List.replicate 9 (popOp .buf) ++
  [transferOp .buf .out, pushListOp .out preB,
   pushOp .out false, copyOp .ic .out .tz]

def piecesOut (E : List Bool) (s t x : ℕ) : List Bool :=
  List.replicate (bPv s t + 1 + x * (3 * s + 3)) true ++ [false] ++
  preB ++ ((E.flatMap (bitChunk h0B cfB)).reverse.drop 9).reverse ++
  (List.replicate s cI).flatten ++ cRG ++
  (List.replicate (t + t / 2 + 5) cI).flatten ++ cRG ++
  List.replicate (x * (3 * s + 3)) false

def sD (staging s t x : ℕ) (out : List Bool) : St := fun j => match j with
  | .inp => []
  | .out => out
  | _ => sC [] staging s t x j

theorem piecesOps_sem (E : List Bool) (staging s t x : ℕ) :
    (opList piecesOps).sem (sC E staging s t x) =
      sD staging s t x (piecesOut E s t x) := by
  unfold piecesOps
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [run_push (v := []) rfl]
  rw [run_rep (va := [false]) (vd := []) (vc := List.replicate (x * (3 * s + 3)) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, sC])
    (by simp [Function.update_apply, sC]) (by simp [Function.update_apply, sC])
    (by simp [Function.update_apply, sC])]
  simp only [List.length_replicate, List.append_nil,
    show (List.replicate (x * (3 * s + 3)) [false]).flatten = List.replicate (x * (3 * s + 3)) false
      by simp [flat_rep_rep]]
  rw [run_clear]
  rw [run_pushList (v := List.replicate (x * (3 * s + 3)) false) (by simp [Function.update_apply])]
  rw [run_pushList (v := []) (by simp [Function.update_apply])]
  simp only [List.append_nil]
  rw [run_rep (va := cI) (vd := cRG ++ List.replicate (x * (3 * s + 3)) false)
    (vc := List.replicate (t + t / 2 + 5) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sC]) (by simp [Function.update_apply, sC])
    (by simp [Function.update_apply, sC])]
  simp only [List.length_replicate]
  rw [run_pushList (v := (List.replicate (t + t / 2 + 5) cI).flatten ++ (cRG ++ List.replicate (x * (3 * s + 3)) false))
    (by simp [Function.update_apply])]
  rw [run_rep (va := cI)
    (vd := cRG ++ ((List.replicate (t + t / 2 + 5) cI).flatten ++ (cRG ++ List.replicate (x * (3 * s + 3)) false)))
    (vc := List.replicate s true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sC]) (by simp [Function.update_apply, sC])
    (by simp [Function.update_apply, sC])]
  simp only [List.length_replicate]
  rw [run_clear]
  rw [run_expand (a := E) (b := [])
    (by simp [Function.update_apply, sC]) (by simp [Function.update_apply])]
  simp only [List.append_nil]
  rw [run_repPop (a := (E.flatMap (bitChunk h0B cfB)).reverse) (by simp [Function.update_apply])]
  rw [run_transfer (a := (E.flatMap (bitChunk h0B cfB)).reverse.drop 9)
    (b := (List.replicate s cI).flatten ++ (cRG ++ ((List.replicate (t + t / 2 + 5) cI).flatten ++ (cRG ++ List.replicate (x * (3 * s + 3)) false))))
    (by simp [Function.update_apply]) (by simp [Function.update_apply])]
  rw [run_pushList (v := ((E.flatMap (bitChunk h0B cfB)).reverse.drop 9).reverse ++
      ((List.replicate s cI).flatten ++ (cRG ++ ((List.replicate (t + t / 2 + 5) cI).flatten ++ (cRG ++ List.replicate (x * (3 * s + 3)) false)))))
    (by simp [Function.update_apply])]
  rw [run_push (v := preB ++ (((E.flatMap (bitChunk h0B cfB)).reverse.drop 9).reverse ++
      ((List.replicate s cI).flatten ++ (cRG ++ ((List.replicate (t + t / 2 + 5) cI).flatten ++ (cRG ++ List.replicate (x * (3 * s + 3)) false))))))
    (by simp [Function.update_apply])]
  rw [run_copy (a := List.replicate (bPv s t + 1 + x * (3 * s + 3)) true)
    (b := false :: (preB ++ (((E.flatMap (bitChunk h0B cfB)).reverse.drop 9).reverse ++
      ((List.replicate s cI).flatten ++ (cRG ++ ((List.replicate (t + t / 2 + 5) cI).flatten ++ (cRG ++ List.replicate (x * (3 * s + 3)) false)))))))
    (by simp [Function.update_apply, sC]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sC])]
  rw [opList_nil_sem]
  funext j; cases j <;> simp [Function.update_apply, sD, sC, piecesOut, List.append_assoc]

/-! ### Phase 5: `rowPrepOps` -/

def oRow (s : ℕ) : List Bool := (List.replicate s c6O).flatten
def otRow (s : ℕ) : List Bool := oRow s ++ ttB
def ztRow (s : ℕ) : List Bool := (List.replicate s c6Z).flatten ++ ttB
def gBlock (s : ℕ) : List Bool := (List.replicate 4 (otRow s)).flatten ++ (ztRow s ++ otRow s)

def rowPrepOps : List Op :=
  [pushListOp .buf c6O, repOp .buf .o .s .tc .tz, clearOp .buf,
   pushListOp .ot ttB, copyOp .o .ot .tz,
   pushListOp .zt ttB, pushListOp .buf c6Z, repOp .buf .zt .s .tc .tz, clearOp .buf,
   copyOp .ot .g .tz, copyOp .zt .g .tz] ++
  List.replicate 4 (copyOp .ot .g .tz)

def sE (staging s t x : ℕ) (out : List Bool) : St := fun j => match j with
  | .o => oRow s
  | .ot => otRow s
  | .zt => ztRow s
  | .g => gBlock s
  | _ => sD staging s t x out j

theorem rowPrepOps_sem (staging s t x : ℕ) (out : List Bool) :
    (opList rowPrepOps).sem (sD staging s t x out) = sE staging s t x out := by
  unfold rowPrepOps
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [run_pushList (v := []) (by simp [sD, sC])]
  simp only [List.append_nil]
  rw [run_rep (va := c6O) (vd := []) (vc := List.replicate s true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, sD, sC])
    (by simp [Function.update_apply, sD, sC]) (by simp [Function.update_apply, sD, sC])
    (by simp [Function.update_apply, sD, sC])]
  simp only [List.length_replicate, List.append_nil]
  rw [run_clear]
  rw [run_pushList (v := []) (by simp [Function.update_apply, sD, sC])]
  simp only [List.append_nil]
  rw [run_copy (a := oRow s) (b := ttB)
    (by simp [Function.update_apply, oRow]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sD, sC])]
  rw [run_pushList (v := []) (by simp [Function.update_apply, sD, sC])]
  simp only [List.append_nil]
  rw [run_pushList (v := []) (by simp [Function.update_apply])]
  simp only [List.append_nil]
  rw [run_rep (va := c6Z) (vd := ttB) (vc := List.replicate s true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sD, sC]) (by simp [Function.update_apply, sD, sC])
    (by simp [Function.update_apply, sD, sC])]
  simp only [List.length_replicate]
  rw [run_clear]
  rw [run_copy (a := otRow s) (b := [])
    (by simp [Function.update_apply, otRow]) (by simp [Function.update_apply, sD, sC])
    (by simp [Function.update_apply, sD, sC])]
  simp only [List.append_nil]
  rw [run_copy (a := ztRow s) (b := otRow s)
    (by simp [Function.update_apply, ztRow]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sD, sC])]
  rw [opList_repCopy 4 .ot .g .tz _ _ _ _ (by simp [Function.update_apply, sD, sC])]
  funext j; cases j <;> simp [Function.update_apply, sE, sD, sC, oRow, otRow, ztRow, gBlock]

/-! ### Phase 6: `boardOps` -/

def aRow (s : ℕ) : List Bool := (List.replicate s c6A).flatten ++ ttB

def boardFlat (staging s t r : ℕ) : List Bool :=
  (List.replicate r (true :: List.replicate (6 * s + 6) false)).flatten ++
  (List.replicate (6 * s + 4) true ++ [false, true, true]) ++
  (List.replicate (6 * s + 4) true ++ [false, false, false]) ++
  (List.replicate 4 (aRow s)).flatten ++
  ztRow s ++ otRow s ++
  (List.replicate (t + 2) (gBlock s)).flatten ++
  (List.replicate 2 (otRow s)).flatten ++
  (oRow s ++ [false, true, true, true, true, true, true]) ++
  (oRow s ++ [false, false, false, true, true, true, true]) ++
  (List.replicate (3 * s + staging) (List.replicate (6 * s + 7) false)).flatten

def boardOps : List Op :=
  [pushOp .ta false, repOp .ta .buf .w .tc .tz, repOp .buf .out .ss .tc .tz, clearOp .buf,
   pushListOp .out [false, false, false, true, true, true, true], copyOp .o .out .tz,
   pushListOp .out [false, true, true, true, true, true, true], copyOp .o .out .tz] ++
  List.replicate 2 (copyOp .ot .out .tz) ++
  [repOp .g .out .t2 .tc .tz,
   copyOp .ot .out .tz, copyOp .zt .out .tz,
   pushListOp .c1 ttB, pushListOp .buf c6A, repOp .buf .c1 .s .tc .tz, clearOp .buf] ++
  List.replicate 4 (copyOp .c1 .out .tz) ++
  [pushListOp .out [false, false, false], copyOp .w4 .out .tz,
   pushListOp .out [false, true, true], copyOp .w4 .out .tz,
   repOp .ta .buf .w6 .tc .tz, pushOp .buf true, repOp .buf .out .r .tc .tz,
   pushOp .out false, copyOp .w .out .tz,
   pushOp .out false, copyOp .h .out .tz]

theorem boardOps_sem_out (staging s t x : ℕ) (out : List Bool) :
    (opList boardOps).sem (sE staging s t x out) .out =
      List.replicate (bbhv staging s t + 2 + 2 * x) true ++ [false] ++
      List.replicate (6 * s + 7) true ++ [false] ++
      boardFlat staging s t (2 * x) ++ out := by
  unfold boardOps
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [run_push (v := []) (by simp [sE, sD, sC])]
  rw [run_rep (va := [false]) (vd := []) (vc := List.replicate (6 * s + 7) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.length_replicate, List.append_nil,
    show (List.replicate (6 * s + 7) [false]).flatten = List.replicate (6 * s + 7) false
      by simp [flat_rep_rep]]
  rw [run_rep (va := List.replicate (6 * s + 7) false) (vd := out)
    (vc := List.replicate (3 * s + staging) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.length_replicate]
  rw [run_clear]
  set out1 := (List.replicate (3 * s + staging) (List.replicate (6 * s + 7) false)).flatten ++ out
  rw [run_pushList (v := out1) (by simp [Function.update_apply])]
  rw [run_copy (a := oRow s) (b := [false, false, false, true, true, true, true] ++ out1)
    (by simp [Function.update_apply, sE]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out2 := oRow s ++ ([false, false, false, true, true, true, true] ++ out1)
  rw [run_pushList (v := out2) (by simp [Function.update_apply])]
  rw [run_copy (a := oRow s) (b := [false, true, true, true, true, true, true] ++ out2)
    (by simp [Function.update_apply, sE]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out3 := oRow s ++ ([false, true, true, true, true, true, true] ++ out2)
  rw [run_repCopy (a := otRow s) (b := out3)
    (by simp [Function.update_apply, sE]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out4 := (List.replicate 2 (otRow s)).flatten ++ out3
  rw [run_rep (va := gBlock s) (vd := out4) (vc := List.replicate (t + 2) true)
    (by simp [Function.update_apply, sE]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.length_replicate]
  set out5 := (List.replicate (t + 2) (gBlock s)).flatten ++ out4
  rw [run_copy (a := otRow s) (b := out5)
    (by simp [Function.update_apply, sE]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  rw [run_copy (a := ztRow s) (b := otRow s ++ out5)
    (by simp [Function.update_apply, sE]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out6 := ztRow s ++ (otRow s ++ out5)
  rw [run_pushList (v := []) (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.append_nil]
  rw [run_pushList (v := []) (by simp [Function.update_apply])]
  simp only [List.append_nil]
  rw [run_rep (va := c6A) (vd := ttB) (vc := List.replicate s true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.length_replicate]
  rw [run_clear]
  rw [run_repCopy (a := aRow s) (b := out6)
    (by simp [Function.update_apply, aRow]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out7 := (List.replicate 4 (aRow s)).flatten ++ out6
  rw [run_pushList (v := out7) (by simp [Function.update_apply])]
  rw [run_copy (a := List.replicate (6 * s + 4) true) (b := [false, false, false] ++ out7)
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out8 := List.replicate (6 * s + 4) true ++ ([false, false, false] ++ out7)
  rw [run_pushList (v := out8) (by simp [Function.update_apply])]
  rw [run_copy (a := List.replicate (6 * s + 4) true) (b := [false, true, true] ++ out8)
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  set out9 := List.replicate (6 * s + 4) true ++ ([false, true, true] ++ out8)
  rw [run_rep (va := [false]) (vd := []) (vc := List.replicate (6 * s + 6) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.length_replicate, List.append_nil,
    show (List.replicate (6 * s + 6) [false]).flatten = List.replicate (6 * s + 6) false
      by simp [flat_rep_rep]]
  rw [run_push (v := List.replicate (6 * s + 6) false) (by simp [Function.update_apply])]
  rw [run_rep (va := true :: List.replicate (6 * s + 6) false) (vd := out9)
    (vc := List.replicate (2 * x) true)
    (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply, sE, sD, sC])
    (by simp [Function.update_apply, sE, sD, sC])]
  simp only [List.length_replicate]
  set out10 := (List.replicate (2 * x) (true :: List.replicate (6 * s + 6) false)).flatten ++ out9
  rw [run_push (v := out10) (by simp [Function.update_apply])]
  rw [run_copy (a := List.replicate (6 * s + 7) true) (b := false :: out10)
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  rw [run_push (v := List.replicate (6 * s + 7) true ++ false :: out10)
    (by simp [Function.update_apply])]
  rw [run_copy (a := List.replicate (bbhv staging s t + 2 + 2 * x) true)
    (b := false :: (List.replicate (6 * s + 7) true ++ false :: out10))
    (by simp [Function.update_apply, sE, sD, sC]) (by simp [Function.update_apply])
    (by simp [Function.update_apply, sE, sD, sC])]
  rw [opList_nil_sem]
  simp only [Function.update_self, out10, out9, out8, out7, out6, out5, out4, out3, out2, out1,
    boardFlat, List.append_assoc, List.cons_append, List.nil_append]

/-! ### Full program -/

def fullProg (staging k : ℕ) : Op :=
  opList (numOps1 staging ++ powOps k ++ numOps2 staging ++ piecesOps ++ rowPrepOps ++ boardOps)

theorem fullProg_sem_out (E : List Bool) (staging k s t : ℕ) :
    (fullProg staging k).sem
      (initSt (List.replicate s true ++ false :: (List.replicate t true ++ false :: E))) .out =
      List.replicate (bbhv staging s t + 2 + 2 * Bv staging s t ^ k) true ++ [false] ++
      List.replicate (6 * s + 7) true ++ [false] ++
      boardFlat staging s t (2 * Bv staging s t ^ k) ++
      piecesOut E s t (Bv staging s t ^ k) := by
  unfold fullProg
  simp only [opList_append]
  rw [numOps1_sem, ← sAx_one, powOps_sem, one_mul, numOps2_sem, piecesOps_sem, rowPrepOps_sem,
    boardOps_sem_out]

/-! ### Mathematical equivalence with `reservoirGame` -/

section equiv
open TetrisHard.Rows

theorem length_flatten_replicate_gen {α : Type*} (n : ℕ) (l : List α) :
    (List.replicate n l).flatten.length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]; ring

theorem integerBlock_length (a : ℕ) : (integerBlock a).length = 5 + 5 * a := by
  simp only [integerBlock, List.length_append, length_flatten_replicate_gen]
  change 3 + a * 5 + 2 = 5 + 5 * a
  ring

theorem numberPieces_length (P : ThreePartition) (hP : P.Valid) :
    (numberPieces P).length = 15 * P.s + 5 * (P.s * P.target) := by
  unfold numberPieces
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, integerBlock_length, List.sum_ofFn]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, hP.1]
  ring

theorem basePieces_length (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) :
    (basePieces P).length = bPv P.s P.target := by
  unfold basePieces bPv
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  rw [numberPieces_length P hP]
  obtain ⟨m, hm⟩ := hN.2.1
  have hdiv : 3 * P.target / 2 = P.target + P.target / 2 := by omega
  rw [hdiv]
  ring

theorem baseBoard_height (P : ThreePartition) (staging : ℕ) :
    (baseBoard P staging).height = bbhv staging P.s P.target := by
  simp [baseBoard, baseHeight, bbhv]; ring

theorem noBound_eq (P : ThreePartition) (staging : ℕ) (hP : P.Valid) (hN : P.Normalized) :
    noBound P staging = nbv staging P.s P.target := by
  unfold noBound nbv
  rw [baseBoard_height, basePieces_length P hP hN]
  ring

theorem pieceFactor_eq (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) :
    pieceFactor P = pfv P.s P.target := by
  unfold pieceFactor pfv
  rw [basePieces_length P hP hN]

theorem gapRows_eq (P : ThreePartition) (staging k : ℕ) (hP : P.Valid) (hN : P.Normalized) :
    gapRows P staging k = 2 * Bv staging P.s P.target ^ k := by
  unfold gapRows Bv
  rw [noBound_eq P staging hP hN, pieceFactor_eq P hP hN]

theorem sqCount_eq (s x : ℕ) : 2 * x * (6 * s + 6) / 4 = x * (3 * s + 3) := by
  have h : 2 * x * (6 * s + 6) = 4 * (x * (3 * s + 3)) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by decide)]

theorem unaryCode_append (l1 l2 : List ℕ) :
    unaryCode (l1 ++ l2) = unaryCode l1 ++ unaryCode l2 := by
  simp [unaryCode]

theorem unaryCode_cons (n : ℕ) (ns : List ℕ) :
    unaryCode (n :: ns) = List.replicate n true ++ false :: unaryCode ns := by
  simp [unaryCode]

theorem unaryCode_replicate (n a : ℕ) :
    unaryCode (List.replicate n a) =
      (List.replicate n (List.replicate a true ++ [false])).flatten := by
  induction n with
  | zero => simp [unaryCode]
  | succ n ih =>
    rw [List.replicate_succ, unaryCode_cons, List.replicate_succ, List.flatten_cons, ih]
    simp [List.append_assoc]

theorem flatMap_bitChunk_rep (a : ℕ) (c0 c1 : List Bool) :
    (List.replicate a true).flatMap (bitChunk c0 c1) = (List.replicate a c1).flatten := by
  induction a with
  | zero => simp
  | succ a ih => simp [List.replicate_succ, bitChunk, ih]

theorem integerBlock_code (a : ℕ) :
    unaryCode ((integerBlock a).map Piece.code) =
      preB ++ (List.replicate a cfB).flatten ++ [false, false] := by
  unfold integerBlock
  simp only [List.map_append, unaryCode_append]
  have hinit : unaryCode (initiator.map Piece.code) = preB := rfl
  have hterm : unaryCode (terminator.map Piece.code) = [false, false] := rfl
  have hfill : unaryCode ((List.replicate a filler).flatten.map Piece.code) =
      (List.replicate a cfB).flatten := by
    induction a with
    | zero => simp [unaryCode]
    | succ a ih =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append, unaryCode_append, ih,
        List.replicate_succ, List.flatten_cons]
      rfl
  rw [hinit, hfill, hterm]

theorem expand_unaryCode (ns : List ℕ) :
    preB ++ (unaryCode ns).flatMap (bitChunk h0B cfB) =
      unaryCode ((ns.flatMap integerBlock).map Piece.code) ++ preB := by
  induction ns with
  | nil => simp [unaryCode]
  | cons a ns ih =>
    rw [unaryCode_cons, List.flatMap_append, flatMap_bitChunk_rep, List.flatMap_cons]
    have hh : bitChunk h0B cfB false = [false, false] ++ preB := rfl
    rw [hh]
    simp only [List.flatMap_cons, List.map_append, unaryCode_append, integerBlock_code,
      List.append_assoc]
    rw [ih]

theorem numberPieces_code (P : ThreePartition) (hs : 0 < P.s) :
    preB ++ (((unaryCode (List.ofFn P.entry)).flatMap (bitChunk h0B cfB)).reverse.drop 9).reverse =
      unaryCode ((numberPieces P).map Piece.code) := by
  have hne : List.ofFn P.entry ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  obtain ⟨a, as, heq⟩ := List.exists_cons_of_ne_nil hne
  unfold numberPieces
  rw [heq]
  have hexp := expand_unaryCode (a :: as)
  set restU := (List.replicate a cfB).flatten ++ [false, false] ++
    unaryCode ((as.flatMap integerBlock).map Piece.code)
  have hu : unaryCode (((a :: as).flatMap integerBlock).map Piece.code) = preB ++ restU := by
    simp only [List.flatMap_cons, List.map_append, unaryCode_append, integerBlock_code, restU,
      List.append_assoc]
  rw [hu, List.append_assoc] at hexp
  have hflat : (unaryCode (a :: as)).flatMap (bitChunk h0B cfB) = restU ++ preB :=
    List.append_cancel_left hexp
  rw [hflat, List.reverse_append]
  have hlen : preB.reverse.length = 9 := rfl
  rw [List.drop_append_of_le_length (by omega)]
  have hd : preB.reverse.drop 9 = [] := rfl
  rw [hd, List.nil_append, List.reverse_reverse, hu]

theorem piecesOut_eq (P : ThreePartition) (staging k : ℕ)
    (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s) :
    piecesOut (unaryCode (List.ofFn P.entry)) P.s P.target (Bv staging P.s P.target ^ k) =
      unaryCode ((reservoirGame P staging (gapRows P staging k)).pieces.length ::
        (reservoirGame P staging (gapRows P staging k)).pieces.map Piece.code) := by
  set x := Bv staging P.s P.target ^ k
  have hr : gapRows P staging k = 2 * x := gapRows_eq P staging k hP hN
  have hsq : gapRows P staging k * (6 * P.s + 6) / 4 = x * (3 * P.s + 3) := by
    rw [hr]; exact sqCount_eq P.s x
  have hlen : (reservoirGame P staging (gapRows P staging k)).pieces.length =
      bPv P.s P.target + 1 + x * (3 * P.s + 3) := by
    simp [reservoirGame, basePieces_length P hP hN, hsq]; omega
  obtain ⟨m, hm⟩ := hN.2.1
  have hdiv : 3 * P.target / 2 + 5 = P.target + P.target / 2 + 5 := by omega
  rw [unaryCode_cons, hlen]
  simp only [reservoirGame, basePieces, hsq, hdiv, List.map_append, List.map_replicate,
    List.map_cons, List.map_nil, unaryCode_append, unaryCode_replicate, Piece.code]
  have hcRG : unaryCode [2] = cRG := rfl
  have hcI : List.replicate 5 true ++ [false] = cI := rfl
  have hcSq : (List.replicate (x * (3 * P.s + 3)) (List.replicate 0 true ++ [false])).flatten =
      List.replicate (x * (3 * P.s + 3)) false := by
    simp [flat_rep_rep]
  rw [hcRG, hcI, hcSq, ← numberPieces_code P hs]
  simp only [piecesOut, List.append_assoc, List.cons_append, List.nil_append]

/-! ### Board rows equivalence -/

def gRows (s : ℕ) : List (List Bool) :=
  [otRow s, otRow s, otRow s, otRow s, ztRow s, otRow s]

def expectedRows (staging s t r : ℕ) : List (List Bool) :=
  List.replicate r (true :: List.replicate (6 * s + 6) false) ++
  [List.replicate (6 * s + 4) true ++ [false, true, true],
   List.replicate (6 * s + 4) true ++ [false, false, false]] ++
  List.replicate 4 (aRow s) ++
  [ztRow s, otRow s] ++
  (List.replicate (t + 2) (gRows s)).flatten ++
  List.replicate 2 (otRow s) ++
  [oRow s ++ [false, true, true, true, true, true, true],
   oRow s ++ [false, false, false, true, true, true, true]] ++
  List.replicate (3 * s + staging) (List.replicate (6 * s + 7) false)

theorem flatten_flatten_replicate {α : Type*} (n : ℕ) (l : List (List α)) :
    (List.replicate n l).flatten.flatten = (List.replicate n l.flatten).flatten := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.flatten_append, ih]

theorem gRows_flatten (s : ℕ) : (gRows s).flatten = gBlock s := by
  simp [gRows, gBlock, List.replicate_succ, List.append_assoc]

theorem expectedRows_flatten (staging s t r : ℕ) :
    (expectedRows staging s t r).flatten = boardFlat staging s t r := by
  simp only [expectedRows, boardFlat, List.flatten_append, List.flatten_cons, List.flatten_nil,
    flatten_flatten_replicate, gRows_flatten, List.append_nil, List.append_assoc]

theorem row_eq_bucket (s : ℕ) (c tail : List Bool) (hc : c.length = 6) (ht : tail.length = 7)
    (f : Fin (6 * s + 7) → Bool)
    (h1 : ∀ x : ℕ, (hx : x < 6 * s) → f ⟨x, by omega⟩ = c.get ⟨x % 6, by omega⟩)
    (h2 : ∀ k : ℕ, (hk : k < 7) → f ⟨6 * s + k, by omega⟩ = tail.get ⟨k, by omega⟩) :
    List.ofFn f = (List.replicate s c).flatten ++ tail := by
  have hlen : ((List.replicate s c).flatten ++ tail).length = 6 * s + 7 := by
    simp [length_flatten_replicate_gen, hc, ht]; ring
  apply List.ext_getElem (by simp [hlen])
  intro i hi _
  simp only [List.getElem_ofFn]
  have hcl : (List.replicate s c).flatten.length = 6 * s := by
    rw [length_flatten_replicate_gen, hc]; ring
  by_cases hlt : i < 6 * s
  · rw [List.getElem_append_left (by omega)]
    rw [getElem_flatten_replicate s c (by omega) i (by omega)]
    rw [h1 i hlt]
    congr 1; apply Fin.ext; simp [hc]
  · rw [List.getElem_append_right (by omega)]
    have hk : i - 6 * s < 7 := by simp at hi; omega
    have hidx : 6 * s + (i - 6 * s) = i := by omega
    have hf := h2 (i - 6 * s) hk
    simp only [hidx] at hf
    rw [hf, List.get_eq_getElem]
    congr 1; simp [hcl]

theorem bucketInitial_eq_c6A (x y : ℕ) (hy : y < 4) :
    bucketInitial x y = c6A.get ⟨x % 6, Nat.mod_lt x (by decide)⟩ := by
  have hmod : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
  have hy6 : (y + 1) % 6 ≠ 5 := by omega
  rcases hmod with h | h | h | h | h | h <;> simp [bucketInitial, h, hy, hy6, c6A]

theorem bucketInitial_eq_c6Z (x y : ℕ) (hy : 4 ≤ y) (h5 : (y + 1) % 6 = 5) :
    bucketInitial x y = c6Z.get ⟨x % 6, Nat.mod_lt x (by decide)⟩ := by
  have hmod : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
  have hy4 : ¬ (y < 4) := by omega
  rcases hmod with h | h | h | h | h | h <;> simp [bucketInitial, h, hy4, h5, c6Z]

theorem bucketInitial_eq_c6O (x y : ℕ) (hy : 4 ≤ y) (h5 : (y + 1) % 6 ≠ 5) :
    bucketInitial x y = c6O.get ⟨x % 6, Nat.mod_lt x (by decide)⟩ := by
  have hmod : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
  have hy4 : ¬ (y < 4) := by omega
  rcases hmod with h | h | h | h | h | h <;> simp [bucketInitial, h, hy4, h5, c6O]

theorem reservoirBoard_cell_mid (P : ThreePartition) (staging r y x : ℕ)
    {hy : y < (reservoirBoard P staging r).height} {hx : x < (reservoirBoard P staging r).width}
    (h1 : r + 2 ≤ y) (h2 : y < r + 2 + baseHeight P) :
    (reservoirBoard P staging r).cell ⟨y, hy⟩ ⟨x, hx⟩ =
      if x < 6 * P.s then bucketInitial x (y - r - 2)
      else if x = 6 * P.s then decide (y - r - 2 + 2 < baseHeight P)
      else if x = 6 * P.s + 1 then decide (y - r - 2 + 1 < baseHeight P)
      else if x = 6 * P.s + 2 then decide (y - r - 2 + 2 = baseHeight P)
      else true := by
  simp only [reservoirBoard]
  have hn1 : ¬ (y < r) := by omega
  have hn2 : ¬ (y = r) := by omega
  have hn3 : ¬ (y = r + 1) := by omega
  simp only [hn1, hn2, hn3, ↓reduceIte]
  by_cases hx3 : x < 6 * P.s + 3
  · simp only [hx3, ↓reduceIte, Board.occupied, baseBoard]
    have hbh : (baseBoard P staging).height = baseHeight P + 3 * P.s + staging := rfl
    have hy0 : 0 ≤ (y : ℤ) - r - 2 ∧ (y : ℤ) - r - 2 < (baseHeight P + 3 * P.s + staging : ℕ) := by
      omega
    have hx0 : 0 ≤ (x : ℤ) ∧ (x : ℤ) < (6 * P.s + 3 : ℕ) := by omega
    simp only [hy0, hx0, and_self, ↓reduceDIte]
    have htoY : ((y : ℤ) - r - 2).toNat = y - r - 2 := by omega
    have htoX : (x : ℤ).toNat = x := by omega
    simp only [htoY, htoX]
    have hlt : ¬ (y - r - 2 ≥ baseHeight P) := by omega
    simp only [hlt, ↓reduceIte]
    by_cases hxs : x < 6 * P.s
    · simp [hxs]
    · by_cases hx0' : x = 6 * P.s
      · simp [hxs, hx0']
      · by_cases hx1' : x = 6 * P.s + 1
        · simp [hxs, hx0', hx1']
        · have hx2' : x = 6 * P.s + 2 := by omega
          simp [hxs, hx0', hx1', hx2']
  · simp only [hx3, ↓reduceIte, h2, decide_true]
    have h1' : ¬ (x < 6 * P.s) := by omega
    have h2' : ¬ (x = 6 * P.s) := by omega
    have h3' : ¬ (x = 6 * P.s + 1) := by omega
    have h4' : ¬ (x = 6 * P.s + 2) := by omega
    simp [h1', h2', h3', h4']

theorem reservoirBoard_rows (P : ThreePartition) (staging r : ℕ) :
    (reservoirBoard P staging r).rows = expectedRows staging P.s P.target r := by
  have hH : (reservoirBoard P staging r).height =
      6 * P.target + 22 + 3 * P.s + staging + 2 + r := by
    simp [reservoirBoard, baseBoard, baseHeight]
  have hElen : (expectedRows staging P.s P.target r).length =
      6 * P.target + 22 + 3 * P.s + staging + 2 + r := by
    simp only [expectedRows, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, length_flatten_replicate_gen]
    change r + 2 + 4 + 2 + (P.target + 2) * 6 + 2 + 2 + (3 * P.s + staging) = _
    ring
  apply List.ext_getElem (by simp [Board.rows, hH, hElen])
  intro y hy _
  simp only [Board.rows, List.getElem_ofFn]
  have hys : y < (reservoirBoard P staging r).height := by simpa [Board.rows] using hy
  -- Helper to extract the y-th row from expectedRows
  have get_exp : (expectedRows staging P.s P.target r)[y]'(by rw [hElen, ← hH]; exact hys) =
      if y < r then true :: List.replicate (6 * P.s + 6) false
      else if y = r then List.replicate (6 * P.s + 4) true ++ [false, true, true]
      else if y = r + 1 then List.replicate (6 * P.s + 4) true ++ [false, false, false]
      else if y < r + 6 then aRow P.s
      else if y = r + 6 then ztRow P.s
      else if y = r + 7 then otRow P.s
      else if y < r + 6 * P.target + 20 then
        if (y - (r + 8)) % 6 = 4 then ztRow P.s else otRow P.s
      else if y < r + 6 * P.target + 22 then otRow P.s
      else if y = r + 6 * P.target + 22 then oRow P.s ++ [false, true, true, true, true, true, true]
      else if y = r + 6 * P.target + 23 then oRow P.s ++ [false, false, false, true, true, true, true]
      else List.replicate (6 * P.s + 7) false := by
    unfold expectedRows
    simp only [List.append_assoc]
    by_cases c1 : y < r
    · simp only [c1, ↓reduceIte]
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
    simp only [c1, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases c2 : y = r
    · subst c2
      simp only [↓reduceIte]
      rw [List.getElem_append_left (by simp)]
      simp
    simp only [c2, ↓reduceIte]
    by_cases c3 : y = r + 1
    · subst c3
      simp only [↓reduceIte]
      rw [List.getElem_append_left (by simp)]
      simp
    simp only [c3, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    by_cases c4 : y < r + 6
    · simp only [c4, ↓reduceIte]
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
    simp only [c4, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases c5 : y = r + 6
    · subst c5
      simp only [↓reduceIte]
      rw [List.getElem_append_left (by simp)]
      have : r + 6 - r - 2 - 4 = 0 := by omega
      simp [this]
    simp only [c5, ↓reduceIte]
    by_cases c6 : y = r + 7
    · subst c6
      simp only [↓reduceIte]
      rw [List.getElem_append_left (by simp)]
      have : r + 7 - r - 2 - 4 = 1 := by omega
      simp [this]
    simp only [c6, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    have hglen : (List.replicate (P.target + 2) (gRows P.s)).flatten.length = 6 * P.target + 12 := by
      rw [length_flatten_replicate_gen]; change (P.target + 2) * 6 = _; ring
    by_cases c7 : y < r + 6 * P.target + 20
    · simp only [c7, ↓reduceIte]
      rw [List.getElem_append_left (by omega)]
      rw [getElem_flatten_replicate (P.target + 2) (gRows P.s) (by simp [gRows]) _ (by omega)]
      have heqidx : y - r - 2 - 4 - 2 = y - (r + 8) := by omega
      have hmod : (y - (r + 8)) % 6 = 0 ∨ (y - (r + 8)) % 6 = 1 ∨ (y - (r + 8)) % 6 = 2 ∨
          (y - (r + 8)) % 6 = 3 ∨ (y - (r + 8)) % 6 = 4 ∨ (y - (r + 8)) % 6 = 5 := by omega
      rcases hmod with h | h | h | h | h | h <;> simp [gRows, heqidx, h]
    simp only [c7, ↓reduceIte]
    rw [List.getElem_append_right (by omega)]
    simp only [hglen]
    by_cases c8 : y < r + 6 * P.target + 22
    · simp only [c8, ↓reduceIte]
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
    simp only [c8, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases c9 : y = r + 6 * P.target + 22
    · subst c9
      simp only [↓reduceIte]
      rw [List.getElem_append_left (by simp; omega)]
      have : r + 6 * P.target + 22 - r - 2 - 4 - 2 - (6 * P.target + 12) - 2 = 0 := by omega
      simp [this]
    simp only [c9, ↓reduceIte]
    by_cases c10 : y = r + 6 * P.target + 23
    · subst c10
      simp only [↓reduceIte]
      rw [List.getElem_append_left (by simp; omega)]
      have : r + 6 * P.target + 23 - r - 2 - 4 - 2 - (6 * P.target + 12) - 2 = 1 := by omega
      simp [this]
    simp only [c10, ↓reduceIte]
    rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
  rw [get_exp]
  -- Now prove row equality in each case
  by_cases c1 : y < r
  · simp only [c1, ↓reduceIte]
    apply List.ext_getElem (by simp [reservoirBoard])
    intro x hx _
    simp only [List.getElem_ofFn, reservoirBoard, c1, ↓reduceIte]
    cases x with
    | zero => simp
    | succ x => simp [List.getElem_replicate]
  simp only [c1, ↓reduceIte]
  by_cases c2 : y = r
  · simp only [c2, ↓reduceIte]
    apply List.ext_getElem (by simp [reservoirBoard])
    intro x hx _
    simp only [List.getElem_ofFn, reservoirBoard, c2, lt_irrefl, ↓reduceIte]
    by_cases hx4 : x < 6 * P.s + 4
    · rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
      simp [show x ≠ 6 * P.s + 4 by omega]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate]
      have hx' : x = 6 * P.s + 4 ∨ x = 6 * P.s + 5 ∨ x = 6 * P.s + 6 := by
        simp [reservoirBoard] at hx; omega
      rcases hx' with rfl | rfl | rfl <;> simp
  simp only [c2, ↓reduceIte]
  by_cases c3 : y = r + 1
  · simp only [c3, ↓reduceIte]
    apply List.ext_getElem (by simp [reservoirBoard])
    intro x hx _
    simp only [List.getElem_ofFn, reservoirBoard, c3, show ¬ (r + 1 < r) by omega,
      show ¬ (r + 1 = r) by omega, ↓reduceIte]
    by_cases hx4 : x < 6 * P.s + 4
    · rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
      simp [hx4]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_replicate]
      have hx' : x = 6 * P.s + 4 ∨ x = 6 * P.s + 5 ∨ x = 6 * P.s + 6 := by
        simp [reservoirBoard] at hx; omega
      rcases hx' with rfl | rfl | rfl <;> simp [hx4]
  simp only [c3, ↓reduceIte]
  by_cases c4 : y < r + 6
  · simp only [c4, ↓reduceIte]
    exact row_eq_bucket P.s c6A ttB rfl rfl _
      (fun x hx => by
        refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
        simp only [hx, ↓reduceIte]
        exact bucketInitial_eq_c6A x (y - r - 2) (by omega))
      (fun k hk => by
        refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
          (by unfold baseHeight; omega)).trans ?_
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [baseHeight, ttB] <;> omega)
  simp only [c4, ↓reduceIte]
  by_cases c5 : y = r + 6
  · simp only [c5, ↓reduceIte]
    exact row_eq_bucket P.s c6Z ttB rfl rfl _
      (fun x hx => by
        refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
        simp only [hx, ↓reduceIte]
        exact bucketInitial_eq_c6Z x _ (by omega) (by omega))
      (fun k hk => by
        refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
          (by unfold baseHeight; omega)).trans ?_
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [baseHeight, ttB])
  simp only [c5, ↓reduceIte]
  by_cases c6 : y = r + 7
  · simp only [c6, ↓reduceIte]
    exact row_eq_bucket P.s c6O ttB rfl rfl _
      (fun x hx => by
        refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
        simp only [hx, ↓reduceIte]
        exact bucketInitial_eq_c6O x _ (by omega) (by omega))
      (fun k hk => by
        refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
          (by unfold baseHeight; omega)).trans ?_
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [baseHeight, ttB])
  simp only [c6, ↓reduceIte]
  by_cases c7 : y < r + 6 * P.target + 20
  · simp only [c7, ↓reduceIte]
    by_cases hmod4 : (y - (r + 8)) % 6 = 4
    · simp only [hmod4, ↓reduceIte]
      exact row_eq_bucket P.s c6Z ttB rfl rfl _
        (fun x hx => by
          refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
          simp only [hx, ↓reduceIte]
          exact bucketInitial_eq_c6Z x (y - r - 2) (by omega) (by omega))
        (fun k hk => by
          refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
            (by unfold baseHeight; omega)).trans ?_
          have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
          rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [baseHeight, ttB] <;> omega)
    · simp only [hmod4, ↓reduceIte]
      exact row_eq_bucket P.s c6O ttB rfl rfl _
        (fun x hx => by
          refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
          simp only [hx, ↓reduceIte]
          exact bucketInitial_eq_c6O x (y - r - 2) (by omega) (by omega))
        (fun k hk => by
          refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
            (by unfold baseHeight; omega)).trans ?_
          have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
          rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [baseHeight, ttB] <;> omega)
  simp only [c7, ↓reduceIte]
  by_cases c8 : y < r + 6 * P.target + 22
  · simp only [c8, ↓reduceIte]
    exact row_eq_bucket P.s c6O ttB rfl rfl _
      (fun x hx => by
        refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
        simp only [hx, ↓reduceIte]
        exact bucketInitial_eq_c6O x (y - r - 2) (by omega) (by omega))
      (fun k hk => by
        refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
          (by unfold baseHeight; omega)).trans ?_
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [baseHeight, ttB] <;> omega)
  simp only [c8, ↓reduceIte]
  by_cases c9 : y = r + 6 * P.target + 22
  · simp only [c9, ↓reduceIte]
    exact row_eq_bucket P.s c6O [false, true, true, true, true, true, true] rfl rfl _
      (fun x hx => by
        refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
        simp only [hx, ↓reduceIte]
        exact bucketInitial_eq_c6O x _ (by omega) (by omega))
      (fun k hk => by
        refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
          (by unfold baseHeight; omega)).trans ?_
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [baseHeight] <;> omega)
  simp only [c9, ↓reduceIte]
  by_cases c10 : y = r + 6 * P.target + 23
  · simp only [c10, ↓reduceIte]
    exact row_eq_bucket P.s c6O [false, false, false, true, true, true, true] rfl rfl _
      (fun x hx => by
        refine (reservoirBoard_cell_mid P staging r _ x (by omega) (by unfold baseHeight; omega)).trans ?_
        simp only [hx, ↓reduceIte]
        exact bucketInitial_eq_c6O x _ (by omega) (by omega))
      (fun k hk => by
        refine (reservoirBoard_cell_mid P staging r _ (6 * P.s + k) (by omega)
          (by unfold baseHeight; omega)).trans ?_
        have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [baseHeight] <;> omega)
  simp only [c10, ↓reduceIte]
  -- Top staging rows: all false
  apply List.ext_getElem (by simp [reservoirBoard])
  intro x hx _
  simp only [List.getElem_ofFn, List.getElem_replicate, reservoirBoard]
  have hn1 : ¬ (y < r) := by omega
  have hn2 : ¬ (y = r) := by omega
  have hn3 : ¬ (y = r + 1) := by omega
  have hn4 : ¬ (y < r + 2 + baseHeight P) := by unfold baseHeight; omega
  simp only [hn1, hn2, hn3, ↓reduceIte]
  by_cases hx3 : x < 6 * P.s + 3
  · simp only [hx3, ↓reduceIte, Board.occupied, baseBoard]
    have hy0 : 0 ≤ (y : ℤ) - r - 2 ∧ (y : ℤ) - r - 2 < (baseHeight P + 3 * P.s + staging : ℕ) := by
      unfold baseHeight at *; omega
    have hx0 : 0 ≤ (x : ℤ) ∧ (x : ℤ) < (6 * P.s + 3 : ℕ) := by omega
    simp only [hy0, hx0, and_self, ↓reduceDIte]
    have hge : ((y : ℤ) - r - 2).toNat ≥ baseHeight P := by unfold baseHeight at *; omega
    simp [hge]
  · simp [hx3, hn4]

theorem fullProg_eq_gameCode (P : ThreePartition) (staging k : ℕ)
    (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s) :
    (fullProg staging k).sem (initSt P.code) .out =
      (reservoirGame P staging (gapRows P staging k)).code := by
  have hcode : P.code =
      List.replicate P.s true ++ false ::
        (List.replicate P.target true ++ false :: unaryCode (List.ofFn P.entry)) := by
    simp [ThreePartition.code, unaryCode]
  rw [hcode, fullProg_sem_out]
  rw [piecesOut_eq P staging k hP hN hs]
  rw [← expectedRows_flatten, ← reservoirBoard_rows P staging (2 * Bv staging P.s P.target ^ k)]
  rw [← gapRows_eq P staging k hP hN]
  simp only [Game.code, reservoirGame, reservoirBoard, baseBoard_height, unaryCode_cons,
    unaryCode, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.cons_append,
    List.nil_append]

end equiv

end GameEmit

open TetrisHard.Rows in
theorem gameEmit_polytime (staging k : ℕ) :
    ∃ e : List Bool → List Bool, CookPvsNP.PolyTimeComputable e ∧
      ∀ P : ThreePartition, P.Valid → P.Normalized → 0 < P.s →
        e P.code = (reservoirGame P staging (gapRows P staging k)).code :=
  ⟨fun w => (GameEmit.fullProg staging k).sem (GameEmit.initSt w) .out,
   GameEmit.op_polytime _,
   fun P hP hN hs => GameEmit.fullProg_eq_gameCode P staging k hP hN hs⟩


namespace GapGameAssemble
open TetrisHard.Rows

theorem scale_normalized {P : ThreePartition} (hP : P.Valid) (hs : 0 < P.s) :
    P.scale.Normalized := by
  obtain ⟨s, T, e⟩ := P
  simp only [ThreePartition.scale, ThreePartition.Valid, ThreePartition.Normalized] at hP hs ⊢
  obtain ⟨hsum, hbd⟩ := hP
  have hT : 0 < T := by
    obtain ⟨_, h2⟩ := hbd ⟨0, by omega⟩
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    rw [← Finset.mul_sum] at hA
    have hA' : (∑ i ∈ A, e i) = T := Nat.eq_of_mul_eq_mul_left (by omega) hA
    have hne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hA'
      omega
    have h4 : A.card * T < 4 * T := by
      have : (∑ i ∈ A, T) < ∑ i ∈ A, 4 * e i :=
        Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hbd i).1)
      rw [Finset.sum_const, ← Finset.mul_sum, hA'] at this
      simpa using this
    have h2 : 2 * T < A.card * T := by
      have : (∑ i ∈ A, 2 * e i) < ∑ i ∈ A, T :=
        Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hbd i).2)
      rw [Finset.sum_const, ← Finset.mul_sum, hA'] at this
      simpa using this
    have h4' := lt_of_mul_lt_mul_right h4 (Nat.zero_le _)
    have h2' := lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
    omega
  · exact ⟨3 * s * T, by ring⟩
  · intro A hA
    rw [← Finset.mul_sum] at hA
    have hne : (∑ i ∈ A, e i) ≠ T := by
      intro h; exact hA (by rw [h])
    have key : ((6 * s * T : ℕ) : ℤ) - ∑ i ∈ A, ((6 * s * e i : ℕ) : ℤ) =
        (6 * s : ℤ) * ((T : ℤ) - ((∑ i ∈ A, e i : ℕ) : ℤ)) := by
      push_cast
      rw [mul_sub, Finset.mul_sum]
    rw [key, abs_mul]
    have h1 : (1 : ℤ) ≤ |(T : ℤ) - ((∑ i ∈ A, e i : ℕ) : ℤ)| := by
      have : (T : ℤ) - ((∑ i ∈ A, e i : ℕ) : ℤ) ≠ 0 := by
        intro h0; apply hne; omega
      exact Int.one_le_abs this
    have h6 : (0 : ℤ) ≤ 6 * s := by positivity
    rw [abs_of_nonneg h6]
    nlinarith

theorem normInstance_good (w : List Bool) :
    (normInstance w).Valid ∧ (normInstance w).Normalized ∧ 0 < (normInstance w).s := by
  have hraw : (rawInstance w).Valid ∧ 0 < (rawInstance w).s := by
    unfold rawInstance
    split_ifs with h1 h2
    · exact ⟨(Classical.choose_spec h1).1, (Classical.choose_spec h1).2.1⟩
    · exact ⟨NoBoundPf.yes_valid, by decide⟩
    · exact ⟨NoBoundPf.no_valid, by decide⟩
  exact ⟨(NoBoundPf.normInstance_valid w).1, scale_normalized hraw.1 hraw.2, hraw.2⟩

end GapGameAssemble

open TetrisHard.Rows in
theorem solution (staging k : ℕ) :
    CookPvsNP.PolyTimeComputable (fun w : List Bool => (gapGame staging k w).code) := by
  obtain ⟨e, he_poly, he_eq⟩ := gameEmit_polytime staging k
  have h := CookPvsNP.polyTimeComputable_comp _ _ NoBoundPf.normCode_polytime he_poly
  convert h using 1
  funext w
  simp only [Function.comp]
  obtain ⟨hv, hn, hs⟩ := GapGameAssemble.normInstance_good w
  exact (he_eq (normInstance w) hv hn hs).symm
