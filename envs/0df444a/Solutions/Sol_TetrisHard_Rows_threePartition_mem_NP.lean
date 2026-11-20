-- Prove2me | solution 1 for TetrisHard.Rows.threePartition_mem_NP
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:27:11.325167+00:00
-- url     : https://prove2.me/submissions/4168d240-5f56-4e30-bcf8-bc1dd9da07bd

import Definitions.Def_TetrisHard_Rows_ThreePartition
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible

open CookPvsNP TetrisHard.Rows
set_option linter.unusedSimpArgs false

namespace ThreePartInNPPf

abbrev A := Option (Bool ⊕ Bool)
abbrev K := Fin 17

/-! ### Part 0: Nonempty language is in P -/

private def nonemptyTM : TM A where
  Q := Fin 3
  q₀ := 0
  qaccept := 1
  qreject := 2
  accept_ne_reject := by decide
  δ _ s := match s with
    | some _ => (1, none, .right)
    | none => (2, none, .right)

private theorem tm_run_halting (M : TM A) (c : Cfg A M.Q) (h : M.IsHalting c) :
    ∀ n, M.run n c = c
  | 0 => rfl
  | n + 1 => by
      simp only [TM.run, Function.iterate_succ_apply]
      rw [TM.step, if_pos h]
      exact tm_run_halting M c h n

private theorem nonemptyTM_step_init (w : List A) :
    (nonemptyTM.step (nonemptyTM.init w)).state =
      if w = [] then nonemptyTM.qreject else nonemptyTM.qaccept := by
  have hnh : ¬ nonemptyTM.IsHalting (nonemptyTM.init w) := by
    simp [TM.IsHalting, TM.init, nonemptyTM]
  rw [TM.step, if_neg hnh]
  cases w with
  | nil => simp [TM.init, nonemptyTM]
  | cons a t => simp [TM.init, nonemptyTM]

private theorem nonemptyTM_halting_step (w : List A) :
    nonemptyTM.IsHalting (nonemptyTM.step (nonemptyTM.init w)) := by
  rw [TM.IsHalting, nonemptyTM_step_init]
  split_ifs <;> simp [nonemptyTM]

theorem nonempty_mem_P : { l : List A | l ≠ [] } ∈ CookPvsNP.P A := by
  refine ⟨A, inferInstance, Function.Embedding.refl A, nonemptyTM, 1, ?_, ?_⟩
  · intro w
    have hmap : w.map (Function.Embedding.refl A) = w := List.map_id w
    rw [hmap, TM.HaltsWithin, pow_one, TM.run, Function.iterate_succ_apply]
    change nonemptyTM.IsHalting (nonemptyTM.run w.length (nonemptyTM.step (nonemptyTM.init w)))
    rw [tm_run_halting nonemptyTM _ (nonemptyTM_halting_step w)]
    exact nonemptyTM_halting_step w
  · intro w
    have hmap : w.map (Function.Embedding.refl A) = w := List.map_id w
    rw [hmap, Set.mem_ofPred_eq, TM.Accepts]
    constructor
    · intro hw
      refine ⟨1, ?_⟩
      simp only [TM.run, Function.iterate_one, nonemptyTM_step_init, if_neg hw]
    · rintro ⟨n, hn⟩ hw
      subst hw
      cases n with
      | zero => simp [TM.run, TM.init, nonemptyTM] at hn
      | succ m =>
        rw [TM.run, Function.iterate_succ_apply] at hn
        change (nonemptyTM.run m (nonemptyTM.step (nonemptyTM.init []))).state = nonemptyTM.qaccept at hn
        rw [tm_run_halting nonemptyTM _ (nonemptyTM_halting_step [])] at hn
        rw [nonemptyTM_step_init] at hn
        simp [nonemptyTM] at hn

/-! ### Part 1: Stack program execution infrastructure -/

def st (b : K → List A) (r : K → ℕ) : K → List A :=
  fun k => List.replicate (r k) none ++ b k

def Run (p : StackProg K A) (s t : K → List A) (B : ℕ) : Prop :=
  ∃ n ≤ B, p.Exec s t n

theorem Run.mono {p : StackProg K A} {s t : K → List A} {B B' : ℕ}
    (h : Run p s t B) (hB : B ≤ B') : Run p s t B' := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨n, hn.trans hB, he⟩

theorem Run.seq {p q : StackProg K A} {s t u : K → List A} {B C : ℕ}
    (h1 : Run p s t B) (h2 : Run q t u C) : Run (.seq p q) s u (B + 1 + C) := by
  obtain ⟨n, hn, he⟩ := h1; obtain ⟨m, hm, hf⟩ := h2
  exact ⟨n + 1 + m, by omega, .seq he hf⟩

theorem Run.branchT {test : (K → Option A) → Bool} {p q : StackProg K A}
    {s t : K → List A} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true) (h : Run p s t B) :
    Run (.branch test p q) s t (1 + B) := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨1 + n, by omega, .branchTrue ht he⟩

theorem Run.branchF {test : (K → Option A) → Bool} {p q : StackProg K A}
    {s t : K → List A} {B : ℕ}
    (ht : test (fun k => (s k).head?) = false) (h : Run q s t B) :
    Run (.branch test p q) s t (1 + B) := by
  obtain ⟨n, hn, he⟩ := h; exact ⟨1 + n, by omega, .branchFalse ht he⟩

theorem Run.loopF {test : (K → Option A) → Bool} {p : StackProg K A}
    {s : K → List A} (ht : test (fun k => (s k).head?) = false) :
    Run (.loop test p) s s 1 := ⟨1, le_rfl, .loopFalse ht⟩

theorem Run.loopT {test : (K → Option A) → Bool} {p : StackProg K A}
    {s t u : K → List A} {B C : ℕ}
    (ht : test (fun k => (s k).head?) = true) (h1 : Run p s t B)
    (h2 : Run (.loop test p) t u C) : Run (.loop test p) s u (1 + B + 1 + C) := by
  obtain ⟨n, hn, he⟩ := h1; obtain ⟨m, hm, hf⟩ := h2
  exact ⟨1 + n + 1 + m, by omega, .loopTrue ht he hf⟩

theorem Run.congr {p : StackProg K A} {s t t' : K → List A} {B : ℕ}
    (h : Run p s t B) (e : t = t') : Run p s t' B := e ▸ h

def noop : StackProg K A := .act (fun _ _ => .keep)

theorem run_noop (s : K → List A) : Run noop s s 1 := ⟨1, le_rfl, .act _ s⟩

theorem head_st (b : K → List A) (r : K → ℕ) (k : K) :
    (st b r k).head? = if 0 < r k then some none else (b k).head? := by
  unfold st; cases r k <;> simp [List.replicate_succ]

theorem head_st_nil {b : K → List A} (r : K → ℕ) {k : K} (hb : b k = []) :
    (st b r k).head? = if 0 < r k then some none else none := by
  rw [head_st, hb]; rfl

theorem run_push (b : K → List A) (r : K → ℕ) (k : K) :
    Run (pushProg k none) (st b r) (st b (Function.update r k (r k + 1))) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).1 none
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, List.replicate_succ]
  · simp [st, Function.update_of_ne hj]

theorem run_pushB (b : K → List A) (r : K → ℕ) (k : K) (a : A) :
    Run (pushProg k a) (st b r)
      (st (Function.update b k (a :: st b r k)) (Function.update r k 0)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).1 a
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st]
  · simp [st, Function.update_of_ne hj]

theorem run_pop (b : K → List A) (r : K → ℕ) (k : K) (n : ℕ) (hk : r k = n + 1) :
    Run (popProg k) (st b r) (st b (Function.update r k n)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).2.1
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, hk, List.replicate_succ]
  · simp [st, Function.update_of_ne hj]

theorem run_popB (b : K → List A) (r : K → ℕ) (k : K) (hk : r k = 0) :
    Run (popProg k) (st b r) (st (Function.update b k (b k).tail) r) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  have h := (stack_basic_macros k (st b r)).2.1
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, hk]
  · simp [st, Function.update_of_ne hj]

theorem run_clear (b : K → List A) (r : K → ℕ) (k : K) (hb : b k = []) :
    Run (clearProg k) (st b r) (st b (Function.update r k 0)) (3 * r k + 1) := by
  have h := (stack_basic_macros k (st b r)).2.2
  rw [show (st b r k).length = r k by simp [st, hb]] at h
  refine ⟨_, le_rfl, ?_⟩
  convert h using 1
  funext j
  by_cases hj : j = k
  · subst hj; simp [st, hb]
  · simp [st, Function.update_of_ne hj]

theorem run_copy (b : K → List A) (r : K → ℕ) (src dst scr : K)
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

theorem run_copyB (b : K → List A) (r : K → ℕ) (src dst scr : K)
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

theorem run_move (b : K → List A) (r : K → ℕ) (src dst : K) (hne : src ≠ dst)
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

theorem run_moveB (b : K → List A) (r : K → ℕ) (src dst : K) (hne : src ≠ dst)
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

theorem run_sync (b : K → List A) (r : K → ℕ) (i j : K) (hne : i ≠ j)
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

theorem run_repeat (b : K → List A) (r : K → ℕ) (e : Fin 4 ↪ K)
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

def Clean (b : K → List A) : Prop := ∀ j : K, 2 ≤ j.val → j.val ≤ 13 → b j = []

theorem Clean.upd {b : K → List A} (hb : Clean b) (j : K) (hj : j.val < 2 ∨ 13 < j.val)
    (x : List A) : Clean (Function.update b j x) := by
  intro i h1 h2
  have : i ≠ j := by rintro rfl; omega
  rw [Function.update_of_ne this]; exact hb i h1 h2

def condPush (j k : K) : StackProg K A :=
  .branch (fun h => (h j).isSome) noop (pushProg k none)

theorem run_condPush (b : K → List A) (r : K → ℕ) (j k : K) (hbj : b j = []) :
    Run (condPush j k) (st b r) (st b (Function.update r k (r k + if 0 < r j then 0 else 1))) 2 := by
  by_cases h : 0 < r j
  · have := Run.branchT (q := pushProg k none) (test := fun h => (h j).isSome)
      (by simp [head_st_nil r hbj, h]) (run_noop (st b r))
    refine this.congr ?_
    simp [h]
  · have := Run.branchF (p := noop) (test := fun h => (h j).isSome)
      (by simp [head_st_nil r hbj, h]) (run_push b r k)
    refine this.congr ?_
    simp [h]

/-! ### Part 2: Phase 1 — Splitting `s` into `w` and `y` -/

def isInl : Option A → Bool
  | some (some (Sum.inl _)) => true
  | _ => false

def isInr : Option A → Bool
  | some (some (Sum.inr _)) => true
  | _ => false

def isSep : Option A → Bool
  | some none => true
  | _ => false

def takeInl : List A → List Bool × List A
  | some (Sum.inl x) :: rest => let p := takeInl rest; (x :: p.1, p.2)
  | l => ([], l)

def takeInr : List A → List Bool × List A
  | some (Sum.inr x) :: rest => let p := takeInr rest; (x :: p.1, p.2)
  | l => ([], l)

theorem takeInl_spec (l : List A) :
    l = (takeInl l).1.map (some ∘ Sum.inl) ++ (takeInl l).2 ∧
    (takeInl l).1.length + (takeInl l).2.length = l.length := by
  induction l with
  | nil => simp [takeInl]
  | cons a rest ih =>
    cases a with
    | none => simp [takeInl]
    | some v =>
      cases v with
      | inl b =>
        simp only [takeInl, List.map_cons, List.cons_append, List.length_cons, Function.comp_apply]
        exact ⟨congrArg (some (Sum.inl b) :: ·) ih.1, by omega⟩
      | inr b => simp [takeInl]

theorem takeInr_spec (l : List A) :
    l = (takeInr l).1.map (some ∘ Sum.inr) ++ (takeInr l).2 ∧
    (takeInr l).1.length + (takeInr l).2.length = l.length := by
  induction l with
  | nil => simp [takeInr]
  | cons a rest ih =>
    cases a with
    | none => simp [takeInr]
    | some v =>
      cases v with
      | inl b => simp [takeInr]
      | inr b =>
        simp only [takeInr, List.map_cons, List.cons_append, List.length_cons, Function.comp_apply]
        exact ⟨congrArg (some (Sum.inr b) :: ·) ih.1, by omega⟩

theorem takeInl_map_sep (w : List Bool) (rest : List A) :
    takeInl (w.map (some ∘ Sum.inl) ++ none :: rest) = (w, none :: rest) := by
  induction w with
  | nil => simp [takeInl]
  | cons b w ih => simp [takeInl, ih]

theorem takeInr_map (y : List Bool) :
    takeInr (y.map (some ∘ Sum.inr)) = (y, []) := by
  induction y with
  | nil => simp [takeInr]
  | cons b y ih => simp [takeInr, ih]

def popTo (src dst : K) : StackProg K A :=
  .act (transferAct src (fun k => decide (k = dst)))

theorem run_popTo (b : K → List A) (r : K → ℕ) (src dst : K) (hne : src ≠ dst)
    (a : A) (rest : List A) (hbs : b src = a :: rest) (hrs : r src = 0) (hrd : r dst = 0) :
    Run (popTo src dst) (st b r)
      (st (Function.update (Function.update b src rest) dst (a :: b dst)) r) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  unfold popTo
  have h := StackProg.Exec.act (transferAct src (fun k => decide (k = dst))) (st b r)
  convert h using 1
  funext j
  unfold StackProg.applyAct transferAct
  by_cases hj : j = src
  · subst hj; simp [st, hrs, hbs, Function.update_of_ne hne, StackAct.apply]
  · by_cases hj' : j = dst
    · subst hj'; simp [st, hrs, hrd, hbs, hj, StackAct.apply]
    · simp [st, hj, hj', Function.update_of_ne hj, Function.update_of_ne hj', StackAct.apply]

def splitW : StackProg K A := .loop (fun h => isInl (h 0)) (popTo 0 16)
def splitY : StackProg K A := .loop (fun h => isInr (h 0)) (popTo 0 16)

theorem run_splitW : ∀ (l : List A) (b : K → List A) (r : K → ℕ),
    b 0 = l → r 0 = 0 → r 16 = 0 →
    Run splitW (st b r)
      (st (Function.update (Function.update b 0 (takeInl l).2) 16
        (((takeInl l).1.map (some ∘ Sum.inl)).reverse ++ b 16)) r)
      (3 * (takeInl l).1.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro b r h0 r0 _
    have := Run.loopF (p := popTo 0 16) (s := st b r) (test := fun h => isInl (h 0))
      (by simp [st, h0, r0, isInl])
    refine this.congr ?_
    congr 1; funext j; simp [takeInl, Function.update_apply]; split_ifs <;> simp_all
  | cons a rest ih =>
    intro b r h0 r0 r16
    cases a with
    | none =>
      have := Run.loopF (p := popTo 0 16) (s := st b r) (test := fun h => isInl (h 0))
        (by simp [st, h0, r0, isInl])
      refine this.congr ?_
      congr 1; funext j; simp [takeInl, Function.update_apply]; split_ifs <;> simp_all
    | some v =>
      cases v with
      | inr x =>
        have := Run.loopF (p := popTo 0 16) (s := st b r) (test := fun h => isInl (h 0))
          (by simp [st, h0, r0, isInl])
        refine this.congr ?_
        congr 1; funext j; simp [takeInl, Function.update_apply]; split_ifs <;> simp_all
      | inl x =>
        have h1 := run_popTo b r 0 16 (by decide) (some (Sum.inl x)) rest h0 r0 r16
        have h2 := ih (Function.update (Function.update b 0 rest) 16 (some (Sum.inl x) :: b 16)) r
          (by simp) r0 r16
        have := Run.loopT (test := fun h => isInl (h 0)) (by simp [st, h0, r0, isInl]) h1 h2
        refine (this.congr ?_).mono (by simp [takeInl]; omega)
        congr 1; funext j
        by_cases hj : j = 16
        · subst hj; simp [takeInl, Function.update_apply, List.append_assoc]
        · by_cases hj' : j = 0
          · subst hj'; simp [takeInl, Function.update_of_ne hj]
          · simp [Function.update_of_ne hj, Function.update_of_ne hj']

theorem run_splitY : ∀ (l : List A) (b : K → List A) (r : K → ℕ),
    b 0 = l → r 0 = 0 → r 16 = 0 →
    Run splitY (st b r)
      (st (Function.update (Function.update b 0 (takeInr l).2) 16
        (((takeInr l).1.map (some ∘ Sum.inr)).reverse ++ b 16)) r)
      (3 * (takeInr l).1.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro b r h0 r0 _
    have := Run.loopF (p := popTo 0 16) (s := st b r) (test := fun h => isInr (h 0))
      (by simp [st, h0, r0, isInr])
    refine this.congr ?_
    congr 1; funext j; simp [takeInr, Function.update_apply]; split_ifs <;> simp_all
  | cons a rest ih =>
    intro b r h0 r0 r16
    cases a with
    | none =>
      have := Run.loopF (p := popTo 0 16) (s := st b r) (test := fun h => isInr (h 0))
        (by simp [st, h0, r0, isInr])
      refine this.congr ?_
      congr 1; funext j; simp [takeInr, Function.update_apply]; split_ifs <;> simp_all
    | some v =>
      cases v with
      | inl x =>
        have := Run.loopF (p := popTo 0 16) (s := st b r) (test := fun h => isInr (h 0))
          (by simp [st, h0, r0, isInr])
        refine this.congr ?_
        congr 1; funext j; simp [takeInr, Function.update_apply]; split_ifs <;> simp_all
      | inr x =>
        have h1 := run_popTo b r 0 16 (by decide) (some (Sum.inr x)) rest h0 r0 r16
        have h2 := ih (Function.update (Function.update b 0 rest) 16 (some (Sum.inr x) :: b 16)) r
          (by simp) r0 r16
        have := Run.loopT (test := fun h => isInr (h 0)) (by simp [st, h0, r0, isInr]) h1 h2
        refine (this.congr ?_).mono (by simp [takeInr]; omega)
        congr 1; funext j
        by_cases hj : j = 16
        · subst hj; simp [takeInr, Function.update_apply, List.append_assoc]
        · by_cases hj' : j = 0
          · subst hj'; simp [takeInr, Function.update_of_ne hj]
          · simp [Function.update_of_ne hj, Function.update_of_ne hj']

/-! ### Part 3: Pure parsing of `w` (adapted from `NoBound.lean`) -/

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

instance : DecidablePred PS.ok := fun q => by unfold PS.ok; infer_instance

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

theorem unaryCode_inj : ∀ ns ms : List ℕ, unaryCode ns = unaryCode ms → ns = ms := by
  intro ns
  induction ns with
  | nil =>
    intro ms h
    cases ms with
    | nil => rfl
    | cons m ms => simp [unaryCode_cons, unaryCode_nil] at h
  | cons n ns ih =>
    intro ms h
    cases ms with
    | nil => simp [unaryCode_cons, unaryCode_nil] at h
    | cons m ms =>
      simp only [unaryCode_cons] at h
      have hnm : n = m := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have := congrArg (·[n]?) h
          have h1 : (List.replicate n true ++ false :: unaryCode ns)[n]? = some false := by
            rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]; rfl
          have h2 : (List.replicate m true ++ false :: unaryCode ms)[n]? = some true := by
            rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos hlt]
          rw [h1, h2] at this; exact absurd this (by decide)
        · have := congrArg (·[m]?) h
          have h1 : (List.replicate n true ++ false :: unaryCode ns)[m]? = some true := by
            rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos hgt]
          have h2 : (List.replicate m true ++ false :: unaryCode ms)[m]? = some false := by
            rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]; rfl
          rw [h1, h2] at this; exact absurd this (by decide)
      subst hnm
      have htail : unaryCode ns = unaryCode ms := by
        have := List.append_cancel_left h
        exact List.cons.inj this |>.2
      exact congrArg (n :: ·) (ih ms htail)

theorem pstep_ct (p : PS) (x : Bool) : (pstep p x).cur + (pstep p x).t ≤ p.cur + p.t + 1 := by
  unfold pstep; split_ifs <;> simp <;> omega

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

/-! ### Part 4: Phase 2 — StackProg for parsing and validating `w` -/

def chk1 : StackProg K A :=
  .seq (copyProg 2 10 12) <| .seq (copyProg 2 10 12) <| .seq (copyProg 2 10 12) <|
  .seq (copyProg 2 10 12) <| .seq (copyProg 4 11 12) <| .seq (syncPopProg 10 11) <|
  .seq (condPush 10 7) <| .seq (clearProg 10) (clearProg 11)

def chk2 : StackProg K A :=
  .seq (copyProg 2 10 12) <| .seq (copyProg 2 10 12) <|
  .seq (copyProg 4 11 12) <| .seq (syncPopProg 10 11) <|
  .seq (condPush 11 7) <| .seq (clearProg 10) (clearProg 11)

theorem run_chk1 (b : K → List A) (hb : Clean b) (r : K → ℕ)
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

theorem run_chk2 (b : K → List A) (hb : Clean b) (r : K → ℕ)
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

def toR (p : PS) : K → ℕ := fun k =>
  if k = 2 then p.cur else if k = 3 then p.s else if k = 4 then p.t else if k = 5 then p.cnt
  else if k = 6 then p.sum else if k = 7 then p.bad else if k = 8 then (if p.f1 then 1 else 0)
  else if k = 9 then (if p.f2 then 1 else 0) else 0

def ENTRY : StackProg K A :=
  .seq chk1 <| .seq chk2 <| .seq (pushProg 5 none) (clearProg 2)

theorem run_entry (b : K → List A) (hb : Clean b) (r : K → ℕ)
    (h10 : r 10 = 0) (h11 : r 11 = 0) (h12 : r 12 = 0) :
    Run ENTRY (st b r) (st b (Function.update (Function.update (Function.update r 7
      (r 7 + badInc (r 4) (r 2))) 5 (r 5 + 1)) 2 0)) (130 * r 2 + 50 * r 4 + 100) := by
  refine Run.mono (Run.congr (Run.seq (run_chk1 b hb r h10 h11 h12) <|
    Run.seq (run_chk2 b hb _ ?_ ?_ ?_) <| Run.seq (run_push _ _ 5) (run_clear _ _ 2 ?_)) ?_) ?_
  all_goals try (first | exact hb _ (by decide) (by decide) | simp [Function.update_apply, h10, h11, h12]; done)
  · congr 1; funext k
    fin_cases k <;> simp [Function.update_apply, badInc] <;> omega
  · simp [Function.update_apply]; omega

def TB : StackProg K A :=
  .seq (popProg 0) <| .seq (pushProg 2 none) (.branch (fun h => (h 9).isSome) (pushProg 6 none) noop)

def FB : StackProg K A :=
  .seq (popProg 0) (.branch (fun h => (h 8).isSome)
    (.branch (fun h => (h 9).isSome) ENTRY
      (.seq (transferProg 2 (fun k => decide (k = 4))) (pushProg 9 none)))
    (.seq (transferProg 2 (fun k => decide (k = 3))) (pushProg 8 none)))

def BODY : StackProg K A :=
  .branch (fun h => decide (h 0 = some (some (Sum.inl true)))) TB FB

theorem run_body (b : K → List A) (hb : Clean b) (x : Bool) (rest : List A)
    (hb0 : b 0 = some (Sum.inl x) :: rest) (p : PS) :
    Run BODY (st b (toR p)) (st (Function.update b 0 rest) (toR (pstep p x)))
      (200 * (p.cur + p.t) + 200) := by
  have hb' : Clean (Function.update b 0 rest) := hb.upd 0 (by decide) _
  have e2 := hb' 2 (by decide) (by decide)
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

def LOOP : StackProg K A := .loop (fun h => (h 0).isSome) BODY

theorem run_loop (L : ℕ) : ∀ (rest : List Bool) (b : K → List A) (p : PS), Clean b →
    b 0 = rest.map (some ∘ Sum.inl) → p.cur + p.t + rest.length ≤ L →
    Run LOOP (st b (toR p)) (st (Function.update b 0 []) (toR (rest.foldl pstep p)))
      (rest.length * (200 * L + 203) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro b p hb hb0 _
    simp only [List.map_nil] at hb0
    have := Run.loopF (p := BODY) (s := st b (toR p)) (test := fun h => (h 0).isSome)
      (by simp [st, toR, hb0])
    refine (this.congr ?_).mono (by simp)
    have : Function.update b 0 [] = b := by rw [← hb0]; exact Function.update_eq_self 0 b
    simp [this]
  | cons x rest ih =>
    intro b p hb hb0 hL
    have h2 := ih (Function.update b 0 (rest.map (some ∘ Sum.inl))) (pstep p x)
      (hb.upd 0 (by decide) _) (by simp) (by have := pstep_ct p x; simp at hL; omega)
    have := Run.loopT (test := fun h => (h 0).isSome) (by simp [st, toR, hb0])
      (run_body b hb x (rest.map (some ∘ Sum.inl)) hb0 p) h2
    refine (this.congr ?_).mono ?_
    · simp
    · simp only [List.length_cons, add_one_mul] at hL ⊢
      omega

def eTP : Fin 4 ↪ K := ⟨![4, 11, 13, 12], by decide⟩

def TP : StackProg K A :=
  .seq (copyProg 3 10 12) <| .seq (copyProg 3 10 12) <| .seq (copyProg 3 10 12) <|
  .seq (syncPopProg 10 5) <| .seq (copyProg 3 13 12) <| .seq (repeatCopyProg eTP)
    (syncPopProg 11 6)

def tpR (q : PS) : K → ℕ :=
  Function.update (Function.update (Function.update (Function.update (toR q)
    10 (3 * q.s - min (3 * q.s) q.cnt)) 5 (q.cnt - min (3 * q.s) q.cnt))
    11 (q.s * q.t - min (q.s * q.t) q.sum)) 6 (q.sum - min (q.s * q.t) q.sum)

theorem run_TP (b : K → List A) (hb : Clean b) (q : PS) :
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

def VT (h : K → Option A) : Bool :=
  (h 9).isSome && (h 2).isNone && (h 7).isNone && (h 10).isNone && (h 5).isNone &&
    (h 11).isNone && (h 6).isNone

theorem VT_eq (b : K → List A) (hb : Clean b) (q : PS) :
    VT (fun k => (st b (tpR q) k).head?) = decide q.ok := by
  have H : ∀ k : K, 2 ≤ k.val → k.val ≤ 13 →
      (st b (tpR q) k).head? = if 0 < tpR q k then some none else none :=
    fun k h1 h2 => head_st_nil _ (hb k h1 h2)
  simp only [VT, H 9 (by decide) (by decide), H 2 (by decide) (by decide),
    H 7 (by decide) (by decide), H 10 (by decide) (by decide), H 5 (by decide) (by decide),
    H 11 (by decide) (by decide), H 6 (by decide) (by decide)]
  simp only [tpR, toR, PS.ok, Function.update_apply]
  clear H
  rcases q with ⟨cur, s, t, cnt, sum, bad, f1, f2⟩
  cases f2 <;> simp <;> split_ifs <;> simp <;> omega

/-! ### Part 5: Phase 3 — Parsing and validating `y` -/

structure YS where
  cur : ℕ
  cnt : ℕ
  bad : ℕ

def ystep (s : ℕ) (p : YS) (x : Bool) : YS :=
  if x then { p with cur := p.cur + 1 }
  else { cur := 0, cnt := p.cnt + 1, bad := p.bad + if p.cur < s then 0 else 1 }

def y0 : YS := ⟨0, 0, 0⟩

def YS.ok (s : ℕ) (q : YS) : Prop := q.cur = 0 ∧ q.bad = 0 ∧ q.cnt = 3 * s

instance (s : ℕ) : DecidablePred (YS.ok s) := fun q => by unfold YS.ok; infer_instance

theorem yfold_rep (s n : ℕ) : ∀ p : YS,
    (List.replicate n true).foldl (ystep s) p = { p with cur := p.cur + n } := by
  induction n with
  | zero => intro p; cases p; simp
  | succ n ih =>
    intro p
    rw [List.replicate_succ, List.foldl_cons, ih]
    cases p; simp [ystep]; omega

theorem yfold_code (s : ℕ) (as : List ℕ) : ∀ p : YS, p.cur = 0 →
    (unaryCode as).foldl (ystep s) p =
      { cur := 0, cnt := p.cnt + as.length,
        bad := p.bad + (as.map (fun a => if a < s then 0 else 1)).sum } := by
  induction as with
  | nil => intro p h0; cases p; simp at h0; subst h0; simp [unaryCode_nil]
  | cons a as ih =>
    intro p h0
    rw [unaryCode_cons, List.foldl_append, yfold_rep, List.foldl_cons]
    cases p; simp only at h0; subst h0
    rw [ih] <;> simp [ystep] <;> omega

theorem yparse_full (s : ℕ) (as : List ℕ) (k : ℕ) :
    (unaryCode as ++ List.replicate k true).foldl (ystep s) y0 =
      ⟨k, as.length, (as.map (fun a => if a < s then 0 else 1)).sum⟩ := by
  rw [List.foldl_append, yfold_code s as y0 rfl, yfold_rep]
  simp [y0]

theorem yparse_ok_iff (s : ℕ) (y : List Bool) :
    (y.foldl (ystep s) y0).ok s ↔
      ∃ assigns : List ℕ, y = unaryCode assigns ∧ assigns.length = 3 * s ∧ ∀ a ∈ assigns, a < s := by
  constructor
  · intro h
    obtain ⟨as, k, rfl⟩ := decomp y
    rw [yparse_full] at h
    obtain ⟨hk, hbad, hcnt⟩ := h
    simp only at hk hbad hcnt
    subst hk
    rw [sum_map_eq_zero] at hbad
    refine ⟨as, by simp, hcnt, fun a ha => ?_⟩
    have := hbad a ha
    by_contra hge
    simp [hge] at this
  · rintro ⟨as, rfl, hlen, hlt⟩
    have : unaryCode as = unaryCode as ++ List.replicate 0 true := by simp
    rw [this, yparse_full]
    refine ⟨rfl, ?_, hlen⟩
    simp only
    rw [sum_map_eq_zero]
    intro a ha
    simp [hlt a ha]

theorem ystep_bound (s : ℕ) (p : YS) (x : Bool) :
    (ystep s p x).cur ≤ p.cur + 1 ∧ (ystep s p x).cnt ≤ p.cnt + 1 := by
  unfold ystep; split_ifs <;> simp <;> omega

theorem yfold_bound (s : ℕ) : ∀ (l : List Bool) (p : YS),
    (l.foldl (ystep s) p).cur ≤ p.cur + l.length ∧
    (l.foldl (ystep s) p).cnt ≤ p.cnt + l.length := by
  intro l
  induction l with
  | nil => intro p; simp
  | cons x l ih =>
    intro p
    have h1 := ih (ystep s p x)
    have h2 := ystep_bound s p x
    simp only [List.foldl_cons, List.length_cons]
    omega

def toYR (s t : ℕ) (q : YS) : K → ℕ := fun k =>
  if k = 2 then q.cur else if k = 3 then s else if k = 4 then t else if k = 5 then q.cnt
  else if k = 7 then q.bad else 0

def YCHK : StackProg K A :=
  .seq (copyProg 2 10 12) <| .seq (copyProg 3 11 12) <| .seq (syncPopProg 10 11) <|
  .seq (condPush 11 7) <| .seq (clearProg 10) <| .seq (clearProg 11) <|
  .seq (pushProg 5 none) (clearProg 2)

def YBODY : StackProg K A :=
  .branch (fun h => decide (h 0 = some (some (Sum.inr true))))
    (.seq (popProg 0) (pushProg 2 none))
    (.seq (popProg 0) YCHK)

theorem run_ybody (s t : ℕ) (b : K → List A) (hb : Clean b) (x : Bool) (rest : List A)
    (hb0 : b 0 = some (Sum.inr x) :: rest) (p : YS) :
    Run YBODY (st b (toYR s t p)) (st (Function.update b 0 rest) (toYR s t (ystep s p x)))
      (20 * (p.cur + s) + 30) := by
  have hb' : Clean (Function.update b 0 rest) := hb.upd 0 (by decide) _
  have htl : Function.update b 0 (b 0).tail = Function.update b 0 rest := by simp [hb0]
  obtain ⟨cur, cnt, bad⟩ := p
  cases x with
  | true =>
    refine Run.mono (Run.congr (Run.branchT ?_ (Run.seq (run_popB _ _ 0 ?_) (run_push _ _ 2))) ?_) ?_
    · simp [st, toYR, hb0]
    · simp [toYR]
    · rw [htl]; congr 1; funext k
      fin_cases k <;> simp [Function.update_apply, toYR, ystep]
    · omega
  | false =>
    refine Run.mono (Run.congr (Run.branchF ?_ (Run.seq (run_popB _ _ 0 ?_) <|
      Run.seq (run_copy _ _ 2 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
      Run.seq (run_copy _ _ 3 11 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
      Run.seq (run_sync _ _ 10 11 (by decide) ?_ ?_) <|
      Run.seq (run_condPush _ _ 11 7 ?_) <|
      Run.seq (run_clear _ _ 10 ?_) <|
      Run.seq (run_clear _ _ 11 ?_) <|
      Run.seq (run_push _ _ 5) (run_clear _ _ 2 ?_))) ?_) ?_
    · simp [st, toYR, hb0]
    · simp [toYR]
    all_goals try (first | rw [htl]; exact hb' _ (by decide) (by decide) | simp [Function.update_apply, toYR]; done)
    · rw [htl]; congr 1; funext k
      fin_cases k <;> simp [Function.update_apply, toYR, ystep] <;> split_ifs <;> omega
    · simp [Function.update_apply, toYR]; omega

def YLOOP : StackProg K A := .loop (fun h => (h 0).isSome) YBODY

theorem run_yloop (s t L : ℕ) (hs : s ≤ L) : ∀ (rest : List Bool) (b : K → List A) (p : YS),
    Clean b → b 0 = rest.map (some ∘ Sum.inr) → p.cur + rest.length ≤ L →
    Run YLOOP (st b (toYR s t p)) (st (Function.update b 0 []) (toYR s t (rest.foldl (ystep s) p)))
      (rest.length * (40 * L + 35) + 1) := by
  intro rest
  induction rest with
  | nil =>
    intro b p hb hb0 _
    simp only [List.map_nil] at hb0
    have := Run.loopF (p := YBODY) (s := st b (toYR s t p)) (test := fun h => (h 0).isSome)
      (by simp [st, toYR, hb0])
    refine (this.congr ?_).mono (by simp)
    have : Function.update b 0 [] = b := by rw [← hb0]; exact Function.update_eq_self 0 b
    simp [this]
  | cons x rest ih =>
    intro b p hb hb0 hL
    have h2 := ih (Function.update b 0 (rest.map (some ∘ Sum.inr))) (ystep s p x)
      (hb.upd 0 (by decide) _) (by simp)
      (by have := (ystep_bound s p x).1; simp at hL; omega)
    have := Run.loopT (test := fun h => (h 0).isSome) (by simp [st, toYR, hb0])
      (run_ybody s t b hb x (rest.map (some ∘ Sum.inr)) hb0 p) h2
    refine (this.congr ?_).mono ?_
    · simp
    · simp only [List.length_cons, add_one_mul] at hL ⊢
      omega

def YTP : StackProg K A :=
  .seq (copyProg 3 10 12) <| .seq (copyProg 3 10 12) <| .seq (copyProg 3 10 12) (syncPopProg 10 5)

def ytpR (s t : ℕ) (q : YS) : K → ℕ :=
  Function.update (Function.update (toYR s t q)
    10 (3 * s - min (3 * s) q.cnt)) 5 (q.cnt - min (3 * s) q.cnt)

theorem run_YTP (s t : ℕ) (b : K → List A) (hb : Clean b) (q : YS) :
    Run YTP (st b (toYR s t q)) (st b (ytpR s t q)) (20 * s + 3 * q.cnt + 20) := by
  refine Run.mono (Run.congr (Run.seq (run_copy _ _ 3 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 3 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_copy _ _ 3 10 12 (by decide) (by decide) (by decide) ?_ ?_ ?_)
      (run_sync _ _ 10 5 (by decide) ?_ ?_)) ?_) ?_
  all_goals try (first | exact hb _ (by decide) (by decide) | simp [Function.update_apply, toYR]; done)
  · congr 1; funext k
    fin_cases k <;> simp [Function.update_apply, toYR, ytpR] <;> omega
  · simp [Function.update_apply, toYR]; omega

def YVT (h : K → Option A) : Bool :=
  (h 2).isNone && (h 7).isNone && (h 10).isNone && (h 5).isNone

theorem YVT_eq (s t : ℕ) (b : K → List A) (hb : Clean b) (q : YS) :
    YVT (fun k => (st b (ytpR s t q) k).head?) = decide (q.ok s) := by
  have H : ∀ k : K, 2 ≤ k.val → k.val ≤ 13 →
      (st b (ytpR s t q) k).head? = if 0 < ytpR s t q k then some none else none :=
    fun k h1 h2 => head_st_nil _ (hb k h1 h2)
  simp only [YVT, H 2 (by decide) (by decide), H 7 (by decide) (by decide),
    H 10 (by decide) (by decide), H 5 (by decide) (by decide)]
  simp only [ytpR, toYR, YS.ok, Function.update_apply]
  clear H
  rcases q with ⟨cur, cnt, bad⟩
  by_cases h1 : cur = 0 <;> by_cases h2 : bad = 0 <;> by_cases h3 : cnt = 3 * s <;>
    simp [h1, h2, h3] <;> omega

/-! ### Part 6: Phase 4 — Verifying bucket sums -/

def bucketSum (j : ℕ) : List ℕ → List ℕ → ℕ
  | e :: es, a :: as => (if a = j then e else 0) + bucketSum j es as
  | _, _ => 0

def badBuckets (T : ℕ) (es assigns : List ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => badBuckets T es assigns m + if bucketSum m es assigns = T then 0 else 1

theorem badBuckets_eq_zero (T : ℕ) (es assigns : List ℕ) :
    ∀ m, badBuckets T es assigns m = 0 ↔ ∀ j < m, bucketSum j es assigns = T
  | 0 => by simp [badBuckets]
  | m + 1 => by
    rw [badBuckets, Nat.add_eq_zero_iff, badBuckets_eq_zero T es assigns m]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
      · exact h1 j hlt
      · by_contra hne; simp [hne] at h2
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), by simp [h m (Nat.lt_succ_self m)]⟩

theorem bucketSum_le_sum (j : ℕ) : ∀ es assigns : List ℕ, bucketSum j es assigns ≤ es.sum
  | [], _ => by simp [bucketSum]
  | _ :: _, [] => by simp [bucketSum]
  | e :: es, a :: as => by
    simp only [bucketSum, List.sum_cons]
    have := bucketSum_le_sum j es as
    split_ifs <;> omega

theorem sum_le_len_unaryCode : ∀ ns : List ℕ, ns.sum ≤ (unaryCode ns).length
  | [] => by simp [unaryCode_nil]
  | n :: ns => by
    rw [unaryCode_cons, List.sum_cons, List.length_append, List.length_replicate, List.length_cons]
    have := sum_le_len_unaryCode ns
    omega

theorem len_le_len_unaryCode : ∀ ns : List ℕ, ns.length ≤ (unaryCode ns).length
  | [] => by simp [unaryCode_nil]
  | n :: ns => by
    rw [unaryCode_cons, List.length_cons, List.length_append, List.length_replicate, List.length_cons]
    have := len_le_len_unaryCode ns
    omega

theorem bucketSum_ofFn (n : ℕ) (f g : Fin n → ℕ) (j : ℕ) :
    bucketSum j (List.ofFn f) (List.ofFn g) =
      ∑ i ∈ Finset.univ.filter (fun i => g i = j), f i := by
  rw [Finset.sum_filter]
  induction n with
  | zero => simp [bucketSum]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, bucketSum, ih, Fin.sum_univ_succ]

def skipLoop (src : K) (tok : A) : StackProg K A :=
  .loop (fun h => decide (h src = some tok)) (popProg src)

def skipNum (src : K) (tok : A) : StackProg K A :=
  .seq (skipLoop src tok) (popProg src)

theorem run_skipLoop (src : K) (tok sep : A) (hne : sep ≠ tok) :
    ∀ (n : ℕ) (rest : List A) (b : K → List A) (r : K → ℕ),
      b src = List.replicate n tok ++ sep :: rest → r src = 0 →
      Run (skipLoop src tok) (st b r)
        (st (Function.update b src (sep :: rest)) r) (3 * n + 1) := by
  intro n
  induction n with
  | zero =>
    intro rest b r hbs hrs
    have := Run.loopF (p := popProg src) (s := st b r)
      (test := fun h => decide (h src = some tok)) (by simp [st, hbs, hrs, hne])
    refine this.congr ?_
    have : Function.update b src (sep :: rest) = b := by
      simp at hbs; rw [← hbs]; exact Function.update_eq_self src b
    simp [this]
  | succ n ih =>
    intro rest b r hbs hrs
    have h1 := run_popB b r src hrs
    have htl : Function.update b src (b src).tail =
        Function.update b src (List.replicate n tok ++ sep :: rest) := by
      simp [hbs, List.replicate_succ]
    rw [htl] at h1
    have h2 := ih rest (Function.update b src (List.replicate n tok ++ sep :: rest)) r (by simp) hrs
    have := Run.loopT (test := fun h => decide (h src = some tok))
      (by simp [st, hbs, hrs, List.replicate_succ]) h1 h2
    refine (this.congr ?_).mono (by omega)
    simp

theorem run_skipNum (src : K) (tok sep : A) (hne : sep ≠ tok)
    (n : ℕ) (rest : List A) (b : K → List A) (r : K → ℕ)
    (hbs : b src = List.replicate n tok ++ sep :: rest) (hrs : r src = 0) :
    Run (skipNum src tok) (st b r) (st (Function.update b src rest) r) (3 * n + 3) := by
  have h1 := run_skipLoop src tok sep hne n rest b r hbs hrs
  have h2 := run_popB (Function.update b src (sep :: rest)) r src hrs
  refine ((h1.seq h2).congr ?_).mono (by omega)
  simp

def readLoop (src dst : K) (tok : A) : StackProg K A :=
  .loop (fun h => decide (h src = some tok)) (.seq (popProg src) (pushProg dst none))

def readNum (src dst : K) (tok : A) : StackProg K A :=
  .seq (readLoop src dst tok) (popProg src)

theorem run_readLoop (src dst : K) (hnd : src ≠ dst) (tok sep : A) (hne : sep ≠ tok) :
    ∀ (n : ℕ) (rest : List A) (b : K → List A) (r : K → ℕ),
      b src = List.replicate n tok ++ sep :: rest → r src = 0 →
      Run (readLoop src dst tok) (st b r)
        (st (Function.update b src (sep :: rest)) (Function.update r dst (r dst + n))) (5 * n + 1) := by
  intro n
  induction n with
  | zero =>
    intro rest b r hbs hrs
    have := Run.loopF (p := .seq (popProg src) (pushProg dst none)) (s := st b r)
      (test := fun h => decide (h src = some tok)) (by simp [st, hbs, hrs, hne])
    refine this.congr ?_
    have : Function.update b src (sep :: rest) = b := by
      simp at hbs; rw [← hbs]; exact Function.update_eq_self src b
    simp [this]
  | succ n ih =>
    intro rest b r hbs hrs
    have h1 := (run_popB b r src hrs).seq (run_push _ r dst)
    have htl : Function.update b src (b src).tail =
        Function.update b src (List.replicate n tok ++ sep :: rest) := by
      simp [hbs, List.replicate_succ]
    rw [htl] at h1
    have h2 := ih rest (Function.update b src (List.replicate n tok ++ sep :: rest))
      (Function.update r dst (r dst + 1)) (by simp)
      (by simp [Function.update_of_ne hnd, hrs])
    have := Run.loopT (test := fun h => decide (h src = some tok))
      (by simp [st, hbs, hrs, List.replicate_succ]) h1 h2
    refine (this.congr ?_).mono (by omega)
    simp only [Function.update_idem]
    congr 1; funext k
    by_cases hk : k = dst
    · subst hk; simp; omega
    · simp [Function.update_of_ne hk]

theorem run_readNum (src dst : K) (hnd : src ≠ dst) (tok sep : A) (hne : sep ≠ tok)
    (n : ℕ) (rest : List A) (b : K → List A) (r : K → ℕ)
    (hbs : b src = List.replicate n tok ++ sep :: rest) (hrs : r src = 0) :
    Run (readNum src dst tok) (st b r)
      (st (Function.update b src rest) (Function.update r dst (r dst + n))) (5 * n + 3) := by
  have h1 := run_readLoop src dst hnd tok sep hne n rest b r hbs hrs
  have h2 := run_popB (Function.update b src (sep :: rest)) (Function.update r dst (r dst + n))
    src (by simp [Function.update_of_ne hnd, hrs])
  refine ((h1.seq h2).congr ?_).mono (by omega)
  simp

def IBODY : StackProg K A :=
  .seq (readNum 0 2 (some (Sum.inl true))) <|
  .seq (readNum 16 5 (some (Sum.inr true))) <|
  .seq (copyProg 8 10 12) <|
  .seq (syncPopProg 5 10) <|
  .seq (.branch (fun h => (h 5).isNone && (h 10).isNone)
    (transferProg 2 (fun k => decide (k = 6))) (clearProg 2)) <|
  .seq (clearProg 5) (clearProg 10)

def ILOOP : StackProg K A := .loop (fun h => (h 16).isSome) IBODY

def toBR (s T acc bad j : ℕ) : K → ℕ := fun k =>
  if k = 3 then s else if k = 4 then T else if k = 6 then acc
  else if k = 7 then bad else if k = 8 then j else 0

theorem run_ibody (s T acc bad j e a L : ℕ) (es as_ : List ℕ)
    (b : K → List A) (hb : Clean b)
    (h0 : b 0 = (unaryCode (e :: es)).map (some ∘ Sum.inl))
    (h16 : b 16 = (unaryCode (a :: as_)).map (some ∘ Sum.inr))
    (he : e ≤ L) (ha : a ≤ L) (hj : j ≤ L) :
    Run IBODY (st b (toBR s T acc bad j))
      (st (Function.update (Function.update b 0 ((unaryCode es).map (some ∘ Sum.inl)))
            16 ((unaryCode as_).map (some ∘ Sum.inr)))
          (toBR s T (acc + if a = j then e else 0) bad j))
      (30 * L + 30) := by
  have h0' : b 0 = List.replicate e (some (Sum.inl true)) ++
      some (Sum.inl false) :: (unaryCode es).map (some ∘ Sum.inl) := by
    rw [h0, unaryCode_cons]; simp
  have h16' : b 16 = List.replicate a (some (Sum.inr true)) ++
      some (Sum.inr false) :: (unaryCode as_).map (some ∘ Sum.inr) := by
    rw [h16, unaryCode_cons]; simp
  set b1 := Function.update b 0 ((unaryCode es).map (some ∘ Sum.inl))
  set b2 := Function.update b1 16 ((unaryCode as_).map (some ∘ Sum.inr))
  have hb2 : Clean b2 := (hb.upd 0 (by decide) _).upd 16 (by decide) _
  set r0 := toBR s T acc bad j
  have h1 := run_readNum 0 2 (by decide) (some (Sum.inl true)) (some (Sum.inl false))
    (by decide) e ((unaryCode es).map (some ∘ Sum.inl)) b r0 h0' (by simp [r0, toBR])
  set r1 := Function.update r0 2 (r0 2 + e)
  have h2 := run_readNum 16 5 (by decide) (some (Sum.inr true)) (some (Sum.inr false))
    (by decide) a ((unaryCode as_).map (some ∘ Sum.inr)) b1 r1
    (by simp [b1, h16']) (by simp [r1, r0, Function.update_apply, toBR])
  set r2 := Function.update r1 5 (r1 5 + a)
  have h3 := run_copy b2 r2 8 10 12 (by decide) (by decide) (by decide)
    (hb2 8 (by decide) (by decide)) (hb2 12 (by decide) (by decide))
    (by simp [r2, r1, r0, Function.update_apply, toBR])
  set r3 := Function.update r2 10 (r2 8 + r2 10)
  have h4 := run_sync b2 r3 5 10 (by decide)
    (hb2 5 (by decide) (by decide)) (hb2 10 (by decide) (by decide))
  set r4 := Function.update (Function.update r3 5 (r3 5 - min (r3 5) (r3 10)))
    10 (r3 10 - min (r3 5) (r3 10))
  by_cases haj : a = j
  · have hbr := Run.branchT (q := clearProg 2)
      (test := fun h => (h 5).isNone && (h 10).isNone)
      (by
        dsimp only
        rw [head_st_nil _ (hb2 5 (by decide) (by decide)),
            head_st_nil _ (hb2 10 (by decide) (by decide))]
        simp [r4, r3, r2, r1, r0, Function.update_apply, toBR, haj])
      (run_move b2 r4 2 6 (by decide) (hb2 2 (by decide) (by decide)))
    set r4' := Function.update (Function.update r4 2 0) 6 (r4 2 + r4 6)
    have h5 := run_clear b2 r4' 5 (hb2 5 (by decide) (by decide))
    set r5 := Function.update r4' 5 0
    have h6 := run_clear b2 r5 10 (hb2 10 (by decide) (by decide))
    refine Run.mono (Run.congr (h1.seq (h2.seq (h3.seq (h4.seq (hbr.seq (h5.seq h6)))))) ?_) ?_
    · congr 1; funext k
      fin_cases k <;> simp [r5, r4', r4, r3, r2, r1, r0, Function.update_apply, toBR, haj] <;> omega
    · simp [r5, r4', r4, r3, r2, r1, r0, Function.update_apply, toBR, haj]; omega
  · have hbr := Run.branchF (p := transferProg 2 (fun k => decide (k = 6)))
      (test := fun h => (h 5).isNone && (h 10).isNone)
      (by
        dsimp only
        rw [head_st_nil _ (hb2 5 (by decide) (by decide)),
            head_st_nil _ (hb2 10 (by decide) (by decide))]
        simp [r4, r3, r2, r1, r0, Function.update_apply, toBR]
        omega)
      (run_clear b2 r4 2 (hb2 2 (by decide) (by decide)))
    set r4' := Function.update r4 2 0
    have h5 := run_clear b2 r4' 5 (hb2 5 (by decide) (by decide))
    set r5 := Function.update r4' 5 0
    have h6 := run_clear b2 r5 10 (hb2 10 (by decide) (by decide))
    refine Run.mono (Run.congr (h1.seq (h2.seq (h3.seq (h4.seq (hbr.seq (h5.seq h6)))))) ?_) ?_
    · congr 1; funext k
      fin_cases k <;> simp [r5, r4', r4, r3, r2, r1, r0, Function.update_apply, toBR, haj] <;> omega
    · simp [r5, r4', r4, r3, r2, r1, r0, Function.update_apply, toBR]; omega

theorem run_iloop (s T bad j L : ℕ) (hj : j ≤ L) :
    ∀ (es as_ : List ℕ) (acc : ℕ) (b : K → List A), Clean b →
      es.length = as_.length →
      b 0 = (unaryCode es).map (some ∘ Sum.inl) →
      b 16 = (unaryCode as_).map (some ∘ Sum.inr) →
      (unaryCode es).length ≤ L → (unaryCode as_).length ≤ L →
      Run ILOOP (st b (toBR s T acc bad j))
        (st (Function.update (Function.update b 0 []) 16 [])
            (toBR s T (acc + bucketSum j es as_) bad j))
        (es.length * (30 * L + 35) + 1) := by
  intro es
  induction es with
  | nil =>
    intro as_ acc b hb hlen h0 h16 _ _
    cases as_ with
    | cons _ _ => simp at hlen
    | nil =>
      have := Run.loopF (p := IBODY) (s := st b (toBR s T acc bad j))
        (test := fun h => (h 16).isSome) (by simp [st, toBR, h16, unaryCode_nil])
      refine (this.congr ?_).mono (by simp)
      simp only [bucketSum, Nat.add_zero]
      congr 1; funext k
      by_cases hk : k = 16
      · subst hk; simp [h16, unaryCode_nil]
      · by_cases hk' : k = 0
        · subst hk'; simp [h0, unaryCode_nil, Function.update_of_ne hk]
        · simp [Function.update_of_ne hk, Function.update_of_ne hk']
  | cons e es ih =>
    intro as_ acc b hb hlen h0 h16 hLe hLa
    cases as_ with
    | nil => simp at hlen
    | cons a as_ =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have he : e ≤ L := by rw [unaryCode_cons] at hLe; simp at hLe; omega
      have ha : a ≤ L := by rw [unaryCode_cons] at hLa; simp at hLa; omega
      have hLe' : (unaryCode es).length ≤ L := by rw [unaryCode_cons] at hLe; simp at hLe; omega
      have hLa' : (unaryCode as_).length ≤ L := by rw [unaryCode_cons] at hLa; simp at hLa; omega
      have h1 := run_ibody s T acc bad j e a L es as_ b hb h0 h16 he ha hj
      have hb2 : Clean (Function.update (Function.update b 0 ((unaryCode es).map (some ∘ Sum.inl)))
          16 ((unaryCode as_).map (some ∘ Sum.inr))) :=
        (hb.upd 0 (by decide) _).upd 16 (by decide) _
      have h2 := ih as_ (acc + if a = j then e else 0) _ hb2 hlen (by simp) (by simp) hLe' hLa'
      have hguard : ((st b (toBR s T acc bad j) 16).head?).isSome = true := by
        simp [st, toBR, h16, unaryCode_cons]
      have := Run.loopT (test := fun h => (h 16).isSome) hguard h1 h2
      refine (this.congr ?_).mono ?_
      · simp only [bucketSum]
        congr 1
        · funext k
          by_cases hk : k = 16
          · subst hk; simp
          · by_cases hk' : k = 0
            · subst hk'; simp [Function.update_of_ne hk]
            · simp [Function.update_of_ne hk, Function.update_of_ne hk']
        · funext k
          unfold toBR; split_ifs <;> omega
      · simp only [List.length_cons, add_one_mul]; omega

def BBODY : StackProg K A :=
  .seq (popProg 8) <|
  .seq (copyProg 14 0 12) <|
  .seq (copyProg 15 16 12) <|
  .seq ILOOP <|
  .seq (copyProg 4 10 12) <|
  .seq (syncPopProg 6 10) <|
  .seq (.branch (fun h => (h 6).isNone && (h 10).isNone) noop (pushProg 7 none)) <|
  .seq (clearProg 6) (clearProg 10)

def BLOOP : StackProg K A := .loop (fun h => (h 8).isSome) BBODY

theorem run_bbody (s T bad j L : ℕ) (es as_ : List ℕ)
    (b : K → List A) (hb : Clean b)
    (h0 : b 0 = []) (h16 : b 16 = [])
    (h14 : b 14 = (unaryCode es).map (some ∘ Sum.inl))
    (h15 : b 15 = (unaryCode as_).map (some ∘ Sum.inr))
    (hlen : es.length = as_.length)
    (hLe : (unaryCode es).length ≤ L) (hLa : (unaryCode as_).length ≤ L)
    (hT : T ≤ L) (hj : j ≤ L) :
    Run BBODY (st b (toBR s T 0 bad (j + 1)))
      (st b (toBR s T 0 (bad + if bucketSum j es as_ = T then 0 else 1) j))
      (40 * L ^ 2 + 100 * L + 50) := by
  have h1 := run_pop b (toBR s T 0 bad (j + 1)) 8 j (by simp [toBR])
  have hupd8 : Function.update (toBR s T 0 bad (j + 1)) 8 j = toBR s T 0 bad j := by
    funext k; fin_cases k <;> simp [Function.update_apply, toBR]
  rw [hupd8] at h1
  have h2 := run_copyB b (toBR s T 0 bad j) 14 0 12 (by decide) (by decide) (by decide)
    (by simp [toBR]) (by simp [toBR]) (hb 12 (by decide) (by decide)) (by simp [toBR])
  set b1 := Function.update b 0 (b 14 ++ b 0)
  have hb1 : Clean b1 := hb.upd 0 (by decide) _
  have h3 := run_copyB b1 (toBR s T 0 bad j) 15 16 12 (by decide) (by decide) (by decide)
    (by simp [toBR]) (by simp [toBR]) (hb1 12 (by decide) (by decide)) (by simp [toBR])
  set b2 := Function.update b1 16 (b1 15 ++ b1 16)
  have hb2 : Clean b2 := hb1.upd 16 (by decide) _
  have h4 := run_iloop s T bad j L hj es as_ 0 b2 hb2 hlen
    (by simp [b2, b1, h0, h14]) (by simp [b2, b1, h16, h15]) hLe hLa
  have hb2_back : Function.update (Function.update b2 0 []) 16 [] = b := by
    funext k
    by_cases hk : k = 16
    · subst hk; simp [h16]
    · by_cases hk' : k = 0
      · subst hk'; simp [h0, Function.update_of_ne hk]
      · simp [b2, b1, Function.update_of_ne hk, Function.update_of_ne hk']
  rw [hb2_back, Nat.zero_add] at h4
  set r4 := toBR s T (bucketSum j es as_) bad j
  have h5 := run_copy b r4 4 10 12
    (by decide) (by decide) (by decide)
    (hb 4 (by decide) (by decide)) (hb 12 (by decide) (by decide)) (by simp [r4, toBR])
  set r5 := Function.update r4 10 (r4 4 + r4 10)
  have h6 := run_sync b r5 6 10 (by decide)
    (hb 6 (by decide) (by decide)) (hb 10 (by decide) (by decide))
  set r6 := Function.update (Function.update r5 6 (r5 6 - min (r5 6) (r5 10)))
    10 (r5 10 - min (r5 6) (r5 10))
  have hbsum : bucketSum j es as_ ≤ L :=
    (bucketSum_le_sum j es as_).trans ((sum_le_len_unaryCode es).trans hLe)
  have hlen_es : es.length ≤ L := (len_le_len_unaryCode es).trans hLe
  have hprod : es.length * (30 * L + 35) ≤ L * (30 * L + 35) :=
    Nat.mul_le_mul_right _ hlen_es
  by_cases hEq : bucketSum j es as_ = T
  · have hbr := Run.branchT (q := pushProg 7 none)
      (test := fun h => (h 6).isNone && (h 10).isNone)
      (by
        dsimp only
        rw [head_st_nil _ (hb 6 (by decide) (by decide)),
            head_st_nil _ (hb 10 (by decide) (by decide))]
        simp [r6, r5, r4, Function.update_apply, toBR, hEq])
      (run_noop (st b r6))
    have h7 := run_clear b r6 6 (hb 6 (by decide) (by decide))
    set r7 := Function.update r6 6 0
    have h8 := run_clear b r7 10 (hb 10 (by decide) (by decide))
    refine Run.mono (Run.congr (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (hbr.seq (h7.seq h8)))))))) ?_) ?_
    · congr 1; funext k
      fin_cases k <;> simp [r7, r6, r5, r4, Function.update_apply, toBR, hEq]
    · simp [b1, r7, r6, r5, r4, Function.update_apply, toBR, h14, h15, hEq]
      nlinarith
  · have hbr := Run.branchF (p := noop)
      (test := fun h => (h 6).isNone && (h 10).isNone)
      (by
        dsimp only
        rw [head_st_nil _ (hb 6 (by decide) (by decide)),
            head_st_nil _ (hb 10 (by decide) (by decide))]
        simp [r6, r5, r4, Function.update_apply, toBR]
        omega)
      (run_push b r6 7)
    set r6' := Function.update r6 7 (r6 7 + 1)
    have h7 := run_clear b r6' 6 (hb 6 (by decide) (by decide))
    set r7 := Function.update r6' 6 0
    have h8 := run_clear b r7 10 (hb 10 (by decide) (by decide))
    refine Run.mono (Run.congr (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (hbr.seq (h7.seq h8)))))))) ?_) ?_
    · congr 1; funext k
      fin_cases k <;> simp [r7, r6', r6, r5, r4, Function.update_apply, toBR, hEq]
    · simp [b1, r7, r6', r6, r5, r4, Function.update_apply, toBR, h14, h15]
      have hmin : min (bucketSum j es as_) T ≤ T := Nat.min_le_right _ _
      have hsub1 : bucketSum j es as_ - min (bucketSum j es as_) T ≤ L := by omega
      have hsub2 : T - min (bucketSum j es as_) T ≤ L := by omega
      nlinarith

theorem run_bloop (s T L : ℕ) (es as_ : List ℕ) (b : K → List A) (hb : Clean b)
    (h0 : b 0 = []) (h16 : b 16 = [])
    (h14 : b 14 = (unaryCode es).map (some ∘ Sum.inl))
    (h15 : b 15 = (unaryCode as_).map (some ∘ Sum.inr))
    (hlen : es.length = as_.length)
    (hLe : (unaryCode es).length ≤ L) (hLa : (unaryCode as_).length ≤ L) (hT : T ≤ L) :
    ∀ (m bad : ℕ), m ≤ L →
      Run BLOOP (st b (toBR s T 0 bad m))
        (st b (toBR s T 0 (bad + badBuckets T es as_ m) 0))
        (m * (40 * L ^ 2 + 100 * L + 55) + 1) := by
  intro m
  induction m with
  | zero =>
    intro bad _
    have := Run.loopF (p := BBODY) (s := st b (toBR s T 0 bad 0))
      (test := fun h => (h 8).isSome)
      (by dsimp only; rw [head_st_nil _ (hb 8 (by decide) (by decide))]; simp [toBR])
    refine (this.congr ?_).mono (by simp)
    simp [badBuckets]
  | succ m ih =>
    intro bad hm
    have h1 := run_bbody s T bad m L es as_ b hb h0 h16 h14 h15 hlen hLe hLa hT (by omega)
    have h2 := ih (bad + if bucketSum m es as_ = T then 0 else 1) (by omega)
    have hguard : ((st b (toBR s T 0 bad (m + 1)) 8).head?).isSome = true := by
      rw [head_st_nil _ (hb 8 (by decide) (by decide))]; simp [toBR]
    have := Run.loopT (test := fun h => (h 8).isSome) hguard h1 h2
    refine (this.congr ?_).mono ?_
    · congr 1; funext k
      fin_cases k <;> simp [toBR, badBuckets]
      omega
    · simp only [add_one_mul]; omega

/-! ### Part 7: Putting all 4 phases together -/

def PHASE4 : StackProg K A :=
  .seq (skipNum 14 (some (Sum.inl true))) <|
  .seq (skipNum 14 (some (Sum.inl true))) <|
  .seq (copyProg 3 8 12) <|
  .seq BLOOP
    (.branch (fun h => (h 7).isNone) (pushProg 1 none) noop)

theorem run_phase4 (P : ThreePartition) (assigns : List ℕ) (L : ℕ)
    (bB : K → List A) (hbB_clean : Clean bB)
    (hbB_0 : bB 0 = []) (hbB_1 : bB 1 = []) (hbB_16 : bB 16 = [])
    (hbB_14 : bB 14 = P.code.map (some ∘ Sum.inl))
    (hbB_15 : bB 15 = (unaryCode assigns).map (some ∘ Sum.inr))
    (halen : assigns.length = 3 * P.s)
    (hLw : P.code.length ≤ L) (hLa : (unaryCode assigns).length ≤ L)
    (hsL : P.s ≤ L) (htL : P.target ≤ L) :
    ∃ S, Run PHASE4 (st bB (toBR P.s P.target 0 0 0)) S
      (45 * L ^ 3 + 120 * L ^ 2 + 90 * L + 30) ∧
      S 1 = if badBuckets P.target (List.ofFn P.entry) assigns P.s = 0 then [none] else [] := by
  set tail1 := List.replicate P.target (some (Sum.inl true)) ++
      some (Sum.inl false) :: (unaryCode (List.ofFn P.entry)).map (some ∘ Sum.inl)
  have hW14 : bB 14 = List.replicate P.s (some (Sum.inl true)) ++
      some (Sum.inl false) :: tail1 := by
    rw [hbB_14, ThreePartition.code]; simp [tail1, unaryCode_cons]
  have hSk1 := run_skipNum 14 (some (Sum.inl true)) (some (Sum.inl false)) (by decide)
    P.s tail1 bB (toBR P.s P.target 0 0 0) hW14 (by simp [toBR])
  have hSk2 := run_skipNum 14 (some (Sum.inl true)) (some (Sum.inl false)) (by decide)
    P.target ((unaryCode (List.ofFn P.entry)).map (some ∘ Sum.inl))
    (Function.update bB 14 tail1) (toBR P.s P.target 0 0 0) (by simp [tail1]) (by simp [toBR])
  set b4 := Function.update bB 14 ((unaryCode (List.ofFn P.entry)).map (some ∘ Sum.inl))
  have hSk2' : Function.update (Function.update bB 14 tail1)
      14 ((unaryCode (List.ofFn P.entry)).map (some ∘ Sum.inl)) = b4 := by simp [b4]
  rw [hSk2'] at hSk2
  have hb4_clean : Clean b4 := hbB_clean.upd 14 (by decide) _
  have hCpS := run_copy b4 (toBR P.s P.target 0 0 0) 3 8 12 (by decide) (by decide) (by decide)
    (hb4_clean 3 (by decide) (by decide)) (hb4_clean 12 (by decide) (by decide)) (by simp [toBR])
  have hCpS_eq : Function.update (toBR P.s P.target 0 0 0) 8
      (toBR P.s P.target 0 0 0 3 + toBR P.s P.target 0 0 0 8) =
      toBR P.s P.target 0 0 P.s := by
    funext k; fin_cases k <;> simp [Function.update_apply, toBR]
  rw [hCpS_eq] at hCpS
  have hLe_es : (unaryCode (List.ofFn P.entry)).length ≤ L := by
    have : (unaryCode (List.ofFn P.entry)).length ≤ P.code.length := by
      rw [ThreePartition.code]; simp [unaryCode_cons]; omega
    omega
  have hBLoop := run_bloop P.s P.target L (List.ofFn P.entry) assigns b4 hb4_clean
    (by simp [b4, hbB_0]) (by simp [b4, hbB_16]) (by simp [b4])
    (by simp [b4, hbB_15]) (by simp [halen]) hLe_es hLa htL P.s 0 hsL
  rw [Nat.zero_add] at hBLoop
  have hL4 : P.s * (40 * L ^ 2 + 100 * L + 55) ≤ 40 * L ^ 3 + 100 * L ^ 2 + 55 * L :=
    (Nat.mul_le_mul_right _ hsL).trans_eq (by ring)
  by_cases hBad : badBuckets P.target (List.ofFn P.entry) assigns P.s = 0
  · have hFin := Run.branchT (q := noop) (test := fun h => (h 7).isNone)
      (by dsimp only; rw [head_st_nil _ (hb4_clean 7 (by decide) (by decide))]; simp [toBR, hBad])
      (run_pushB b4 (toBR P.s P.target 0 (badBuckets P.target (List.ofFn P.entry) assigns P.s) 0) 1 none)
    refine ⟨_, (hSk1.seq (hSk2.seq (hCpS.seq (hBLoop.seq hFin)))).mono ?_, ?_⟩
    · simp [toBR]; omega
    · simp [st, b4, hbB_1, toBR, hBad]
  · have hFin := Run.branchF (p := pushProg 1 none) (test := fun h => (h 7).isNone)
      (by dsimp only; rw [head_st_nil _ (hb4_clean 7 (by decide) (by decide))]; simp [toBR, Nat.pos_of_ne_zero hBad])
      (run_noop (st b4 (toBR P.s P.target 0 (badBuckets P.target (List.ofFn P.entry) assigns P.s) 0)))
    refine ⟨_, (hSk1.seq (hSk2.seq (hCpS.seq (hBLoop.seq hFin)))).mono ?_, ?_⟩
    · simp [toBR]; omega
    · simp [st, b4, hbB_1, toBR, hBad]

def PHASE3 : StackProg K A :=
  .seq (clearProg 8) <|
  .seq (clearProg 9) <|
  .seq (copyProg 15 0 12) <|
  .seq YLOOP <|
  .seq YTP
    (.branch YVT PHASE4 noop)

theorem run_phase3 (P : ThreePartition) (y : List Bool) (L : ℕ)
    (bB : K → List A) (hbB_clean : Clean bB)
    (hbB_0 : bB 0 = []) (hbB_1 : bB 1 = []) (hbB_16 : bB 16 = [])
    (hbB_14 : bB 14 = P.code.map (some ∘ Sum.inl))
    (hbB_15 : bB 15 = y.map (some ∘ Sum.inr))
    (q : PS) (hokW : q.ok) (hqs : q.s = P.s) (hqt : q.t = P.target)
    (hLw : P.code.length ≤ L) (hLy : y.length ≤ L) (hsL : P.s ≤ L) (htL : P.target ≤ L) :
    ∃ S, Run PHASE3 (st bB (tpR q)) S (50 * L ^ 3 + 200 * L ^ 2 + 200 * L + 100) ∧
      S 1 = (open Classical in
        if ∃ assigns : List ℕ, y = unaryCode assigns ∧ assigns.length = 3 * P.s ∧
            (∀ a ∈ assigns, a < P.s) ∧ ∀ j < P.s, bucketSum j (List.ofFn P.entry) assigns = P.target
        then [none] else []) := by
  have hCl8 := run_clear bB (tpR q) 8 (hbB_clean 8 (by decide) (by decide))
  have hCl9 := run_clear bB (Function.update (tpR q) 8 0) 9 (hbB_clean 9 (by decide) (by decide))
  have hR3_eq : Function.update (Function.update (tpR q) 8 0) 9 0 = toYR P.s P.target y0 := by
    obtain ⟨hf2, hcur, hbad, hcnt, hsum⟩ := hokW
    funext k; fin_cases k <;> simp [Function.update_apply, tpR, toR, toYR, y0, hqs, hqt,
      hcur, hbad, hcnt, hsum]
  rw [hR3_eq] at hCl9
  have hCpY := run_copyB bB (toYR P.s P.target y0) 15 0 12 (by decide) (by decide) (by decide)
    (by simp [toYR]) (by simp [toYR]) (hbB_clean 12 (by decide) (by decide)) (by simp [toYR])
  have hCpY_eq : Function.update bB 0 (bB 15 ++ bB 0) =
      Function.update bB 0 (y.map (some ∘ Sum.inr)) := by simp [hbB_15, hbB_0]
  rw [hCpY_eq] at hCpY
  set b3 := Function.update bB 0 (y.map (some ∘ Sum.inr))
  have hb3_clean : Clean b3 := hbB_clean.upd 0 (by decide) _
  have hLoopY := run_yloop P.s P.target L hsL y b3 y0 hb3_clean
    (by simp [b3]) (by simp [y0]; omega)
  have hb3_back : Function.update b3 0 [] = bB := by
    funext k; by_cases hk : k = 0
    · subst hk; simp [hbB_0]
    · simp [b3, Function.update_of_ne hk]
  rw [hb3_back] at hLoopY
  set qy := y.foldl (ystep P.s) y0 with hqy_def
  have hYTP := run_YTP P.s P.target bB hbB_clean qy
  have hyfb : qy.cnt ≤ L := by
    have := (yfold_bound P.s y y0).2
    rw [hqy_def]; simp only [y0] at this ⊢; omega
  have h8le : (if q.f1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h9le : (if q.f2 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hL3 : y.length * (40 * L + 35) ≤ 40 * L ^ 2 + 35 * L :=
    (Nat.mul_le_mul_right _ hLy).trans_eq (by ring)
  by_cases hokY : qy.ok P.s
  · have hYVT : YVT (fun k => (st bB (ytpR P.s P.target qy) k).head?) = true := by
      rw [YVT_eq P.s P.target bB hbB_clean qy]; simp [hokY]
    obtain ⟨assigns, hy_eq, halen, halt⟩ := (yparse_ok_iff P.s y).1 hokY
    have hR4_eq : ytpR P.s P.target qy = toBR P.s P.target 0 0 0 := by
      obtain ⟨hcur, hbad, hcnt⟩ := hokY
      funext k; fin_cases k <;> simp [Function.update_apply, ytpR, toYR, toBR, hcur, hbad, hcnt]
    obtain ⟨S4, hP4, hS4⟩ := run_phase4 P assigns L bB hbB_clean hbB_0 hbB_1 hbB_16
      hbB_14 (hy_eq ▸ hbB_15) halen hLw (hy_eq ▸ hLy) hsL htL
    rw [← hR4_eq] at hP4
    refine ⟨S4, (hCl8.seq (hCl9.seq (hCpY.seq (hLoopY.seq (hYTP.seq (Run.branchT (q := noop) hYVT hP4)))))).mono ?_, ?_⟩
    · simp [hbB_15, tpR, toR, Function.update_apply]; split_ifs <;> omega
    · rw [hS4]
      by_cases hBad : badBuckets P.target (List.ofFn P.entry) assigns P.s = 0
      · have hex : ∃ assigns' : List ℕ, y = unaryCode assigns' ∧ assigns'.length = 3 * P.s ∧
            (∀ a ∈ assigns', a < P.s) ∧ ∀ j < P.s, bucketSum j (List.ofFn P.entry) assigns' = P.target :=
          ⟨assigns, hy_eq, halen, halt, (badBuckets_eq_zero _ _ _ _).1 hBad⟩
        simp [hBad, hex]
      · have hnex : ¬ ∃ assigns' : List ℕ, y = unaryCode assigns' ∧ assigns'.length = 3 * P.s ∧
            (∀ a ∈ assigns', a < P.s) ∧ ∀ j < P.s, bucketSum j (List.ofFn P.entry) assigns' = P.target := by
          rintro ⟨assigns', hy', -, -, hsum'⟩
          have has_eq : assigns = assigns' := unaryCode_inj _ _ (hy_eq.symm.trans hy')
          apply hBad; rw [badBuckets_eq_zero, has_eq]; exact hsum'
        simp [hBad, hnex]
  · have hYVT : YVT (fun k => (st bB (ytpR P.s P.target qy) k).head?) = false := by
      rw [YVT_eq P.s P.target bB hbB_clean qy]; simp [hokY]
    have hnex : ¬ ∃ assigns' : List ℕ, y = unaryCode assigns' ∧ assigns'.length = 3 * P.s ∧
        (∀ a ∈ assigns', a < P.s) ∧ ∀ j < P.s, bucketSum j (List.ofFn P.entry) assigns' = P.target := by
      rintro ⟨assigns', hy', halen', halt', -⟩
      exact hokY (by rw [hqy_def, yparse_ok_iff]; exact ⟨assigns', hy', halen', halt'⟩)
    refine ⟨_, (hCl8.seq (hCl9.seq (hCpY.seq (hLoopY.seq (hYTP.seq
      (Run.branchF (p := PHASE4) hYVT (run_noop (st bB (ytpR P.s P.target qy))))))))).mono ?_, ?_⟩
    · simp [hbB_15, tpR, toR, Function.update_apply]; split_ifs <;> omega
    · simp [st, hbB_1, ytpR, toYR, hnex]

def PHASE2 : StackProg K A :=
  .seq (copyProg 14 0 12) <|
  .seq LOOP <|
  .seq TP
    (.branch VT PHASE3 noop)

def P1a : StackProg K A :=
  .seq splitW (transferProg 16 (fun k => decide (k = 14)))

def P1b : StackProg K A :=
  .seq (popProg 0) (.seq splitY (transferProg 16 (fun k => decide (k = 15))))

def VERIFY : StackProg K A :=
  .seq P1a
    (.branch (fun h => isSep (h 0))
      (.seq P1b (.branch (fun h => (h 0).isNone) PHASE2 noop))
      noop)

/-! ### Part 8: Checking relation `R` and correctness of `VERIFY` -/

def R (w y : List Bool) : Prop :=
  ∃ (P : ThreePartition) (assign : Fin (3 * P.s) → Fin P.s),
    P.Valid ∧
    (∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), P.entry i = P.target) ∧
    w = P.code ∧
    y = unaryCode (List.ofFn (fun i => (assign i).val))

noncomputable def checkFun (s : List A) : List A :=
  open Classical in if s ∈ checkLang R then [none] else []

theorem checkLang_iff_parsed (s : List A) :
    s ∈ checkLang R ↔
      ∃ (w y : List Bool) (P : ThreePartition) (assigns : List ℕ),
        s = w.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr) ∧
        P.Valid ∧ w = P.code ∧
        y = unaryCode assigns ∧ assigns.length = 3 * P.s ∧ (∀ a ∈ assigns, a < P.s) ∧
        ∀ j < P.s, bucketSum j (List.ofFn P.entry) assigns = P.target := by
  constructor
  · rintro ⟨w, y, ⟨P, assign, hV, hA, rfl, rfl⟩, rfl⟩
    refine ⟨P.code, unaryCode (List.ofFn (fun i => (assign i).val)), P,
      List.ofFn (fun i => (assign i).val), rfl, hV, rfl, rfl, by simp, ?_, ?_⟩
    · intro a ha
      rw [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact (assign i).isLt
    · intro j hj
      rw [bucketSum_ofFn]
      convert hA ⟨j, hj⟩ using 2
      ext i; simp [Fin.ext_iff]
  · rintro ⟨w, y, P, assigns, rfl, hV, rfl, rfl, hlen, hlt, hsum⟩
    let assign : Fin (3 * P.s) → Fin P.s :=
      fun i => ⟨assigns[i.val]'(by omega), hlt _ (List.getElem_mem _)⟩
    have hofFn : List.ofFn (fun i => (assign i).val) = assigns := by
      apply List.ext_getElem <;> simp [assign, hlen]
    refine ⟨P.code, unaryCode assigns, ⟨P, assign, hV, ?_, rfl, by rw [hofFn]⟩, rfl⟩
    intro j
    have := hsum j.val j.isLt
    rw [← hofFn, bucketSum_ofFn] at this
    convert this using 2
    ext i; simp [Fin.ext_iff]

theorem verify_run (s : List A) :
    ∃ S B, Run VERIFY (st (fun j => if j = 0 then s else []) (fun _ => 0)) S B ∧
      S 1 = checkFun s ∧ B ≤ 1000 * (s.length + 1) ^ 3 + 1000 := by
  set L := s.length with hL_def
  set b0 : K → List A := fun j => if j = 0 then s else []
  have hSW := run_splitW s b0 (fun _ => 0) (by simp [b0]) rfl rfl
  set w := (takeInl s).1
  set rem1 := (takeInl s).2
  set bSW := Function.update (Function.update b0 0 rem1) 16 ((w.map (some ∘ Sum.inl)).reverse ++ b0 16)
  have hTW := run_moveB bSW (fun _ => 0) 16 14 (by decide) rfl rfl
  have hspec1 := takeInl_spec s
  have hw_len : w.length ≤ L := by
    have := hspec1.2; change w.length + rem1.length = L at this; omega
  have hrem1_len : rem1.length ≤ L := by
    have := hspec1.2; change w.length + rem1.length = L at this; omega
  have hbW_eq : Function.update (Function.update bSW 16 [])
      14 ((bSW 16).reverse ++ bSW 14) =
      Function.update (Function.update b0 0 rem1) 14 (w.map (some ∘ Sum.inl)) := by
    funext k
    by_cases hk : k = 14
    · subst hk; simp [bSW, b0]
    · by_cases hk' : k = 16
      · subst hk'; simp [bSW, b0, Function.update_of_ne hk]
      · by_cases hk'' : k = 0
        · subst hk''; simp [bSW, Function.update_of_ne hk, Function.update_of_ne hk']
        · simp [bSW, Function.update_of_ne hk, Function.update_of_ne hk', Function.update_of_ne hk'']
  have hP1a : Run P1a
      (st b0 (fun _ => 0))
      (st (Function.update (Function.update b0 0 rem1) 14 (w.map (some ∘ Sum.inl))) (fun _ => 0))
      (6 * w.length + 5) := by
    refine ((hSW.seq hTW).congr (congrArg (fun x => st x (fun _ => 0)) hbW_eq)).mono ?_
    simp [bSW, b0]; omega
  set bA := Function.update (Function.update b0 0 rem1) 14 (w.map (some ∘ Sum.inl))
  cases hrem1 : rem1 with
  | nil =>
    have hnot : s ∉ checkLang R := by
      rintro ⟨w', y', -, rfl⟩
      have := takeInl_map_sep w' (y'.map (some ∘ Sum.inr))
      rw [show rem1 = (takeInl (w'.map (some ∘ Sum.inl) ++ none :: y'.map (some ∘ Sum.inr))).2 from rfl,
          this] at hrem1
      simp at hrem1
    refine ⟨_, _, hP1a.seq (Run.branchF (by simp [st, bA, hrem1, isSep]) (run_noop _)), ?_, ?_⟩
    · simp [st, bA, b0, checkFun, hnot]
    · have := Nat.zero_le (L ^ 3); have := Nat.zero_le (L ^ 2); nlinarith
  | cons a1 rem1' =>
    cases a1 with
    | some v1 =>
      have hnot : s ∉ checkLang R := by
        rintro ⟨w', y', -, rfl⟩
        have := takeInl_map_sep w' (y'.map (some ∘ Sum.inr))
        rw [show rem1 = (takeInl (w'.map (some ∘ Sum.inl) ++ none :: y'.map (some ∘ Sum.inr))).2 from rfl,
            this] at hrem1
        simp at hrem1
      refine ⟨_, _, hP1a.seq (Run.branchF (by simp [st, bA, hrem1, isSep]) (run_noop _)), ?_, ?_⟩
      · simp [st, bA, b0, checkFun, hnot]
      · have := Nat.zero_le (L ^ 3); have := Nat.zero_le (L ^ 2); nlinarith
    | none =>
      have hPopSep := run_popB bA (fun _ => 0) 0 rfl
      have htlA : Function.update bA 0 (bA 0).tail = Function.update bA 0 rem1' := by
        simp [bA, hrem1]
      rw [htlA] at hPopSep
      set bA' := Function.update bA 0 rem1'
      have hSY := run_splitY rem1' bA' (fun _ => 0) (by simp [bA']) rfl rfl
      set y := (takeInr rem1').1
      set rem2 := (takeInr rem1').2
      set bSY := Function.update (Function.update bA' 0 rem2) 16 ((y.map (some ∘ Sum.inr)).reverse ++ bA' 16)
      have hTY := run_moveB bSY (fun _ => 0) 16 15 (by decide) rfl rfl
      have hspec2 := takeInr_spec rem1'
      have hy_len : y.length ≤ L := by
        have := hspec2.2; change y.length + rem2.length = rem1'.length at this
        rw [hrem1] at hrem1_len; simp at hrem1_len; omega
      have hbY_eq : Function.update (Function.update bSY 16 [])
          15 ((bSY 16).reverse ++ bSY 15) =
          Function.update (Function.update bA' 0 rem2) 15 (y.map (some ∘ Sum.inr)) := by
        funext k
        by_cases hk : k = 15
        · subst hk; simp [bSY, bA', bA, b0]
        · by_cases hk' : k = 16
          · subst hk'; simp [bSY, bA', bA, b0, Function.update_of_ne hk]
          · by_cases hk'' : k = 0
            · subst hk''; simp [bSY, Function.update_of_ne hk, Function.update_of_ne hk']
            · simp [bSY, Function.update_of_ne hk, Function.update_of_ne hk', Function.update_of_ne hk'']
      set bB := Function.update (Function.update bA' 0 rem2) 15 (y.map (some ∘ Sum.inr))
      have hP1b : Run P1b
          (st bA (fun _ => 0)) (st bB (fun _ => 0)) (6 * y.length + 7) := by
        refine ((hPopSep.seq (hSY.seq hTY)).congr (congrArg (fun x => st x (fun _ => 0)) hbY_eq)).mono ?_
        simp [bSY, bA', bA, b0]; omega
      cases hrem2 : rem2 with
      | cons a2 rem2' =>
        have hnot : s ∉ checkLang R := by
          rintro ⟨w', y', -, rfl⟩
          have h1 := takeInl_map_sep w' (y'.map (some ∘ Sum.inr))
          have hrem1_eq : rem1' = y'.map (some ∘ Sum.inr) := by
            have : rem1 = none :: y'.map (some ∘ Sum.inr) := by
              rw [show rem1 = (takeInl (w'.map (some ∘ Sum.inl) ++ none :: y'.map (some ∘ Sum.inr))).2 from rfl, h1]
            rw [hrem1] at this; exact (List.cons.inj this).2
          have h2 : rem2 = [] := by
            rw [show rem2 = (takeInr rem1').2 from rfl, hrem1_eq, takeInr_map]
          rw [hrem2] at h2; simp at h2
        refine ⟨_, _, hP1a.seq (Run.branchT (by simp [st, bA, hrem1, isSep])
          (hP1b.seq (Run.branchF (by simp [st, bB, hrem2]) (run_noop _)))), ?_, ?_⟩
        · simp [st, bB, bA', bA, b0, checkFun, hnot]
        · have := Nat.zero_le (L ^ 3); have := Nat.zero_le (L ^ 2); nlinarith
      | nil =>
        have hs_eq : s = w.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr) := by
          have h1 : s = w.map (some ∘ Sum.inl) ++ rem1 := hspec1.1
          have h2 : rem1' = y.map (some ∘ Sum.inr) ++ rem2 := hspec2.1
          rw [hrem2, List.append_nil] at h2
          rw [hrem1, h2] at h1
          exact h1
        have hbB_clean : Clean bB := by
          intro k h1 h2
          have hk15 : k ≠ 15 := by rintro rfl; omega
          have hk0 : k ≠ 0 := by rintro rfl; omega
          have hk14 : k ≠ 14 := by rintro rfl; omega
          simp [bB, bA', bA, b0, hk15, hk0, hk14]
        have hbB_0 : bB 0 = [] := by simp [bB, hrem2]
        have hbB_1 : bB 1 = [] := by simp [bB, bA', bA, b0]
        have hbB_14 : bB 14 = w.map (some ∘ Sum.inl) := by simp [bB, bA', bA]
        have hbB_15 : bB 15 = y.map (some ∘ Sum.inr) := by simp [bB]
        have hbB_16 : bB 16 = [] := by simp [bB, bA', bA, b0]
        -- Phase 2: parse and validate w
        have hCpW := run_copyB bB (fun _ => 0) 14 0 12 (by decide) (by decide) (by decide)
          rfl rfl (hbB_clean 12 (by decide) (by decide)) rfl
        have hCpW_eq : Function.update bB 0 (bB 14 ++ bB 0) =
            Function.update bB 0 (w.map (some ∘ Sum.inl)) := by simp [hbB_14, hbB_0]
        rw [hCpW_eq] at hCpW
        have e0 : (fun _ : K => (0 : ℕ)) = toR p0 := by
          funext k; fin_cases k <;> simp [toR, p0]
        set b2 := Function.update bB 0 (w.map (some ∘ Sum.inl))
        have hb2_clean : Clean b2 := hbB_clean.upd 0 (by decide) _
        have hLoopW := run_loop L w b2 p0 hb2_clean (by simp [b2]) (by simp [p0]; omega)
        rw [← e0] at hLoopW
        have hb2_back : Function.update b2 0 [] = bB := by
          funext k; by_cases hk : k = 0
          · subst hk; simp [hbB_0]
          · simp [b2, Function.update_of_ne hk]
        rw [hb2_back] at hLoopW
        set q := w.foldl pstep p0 with hq_def
        have hTP := run_TP bB hbB_clean q
        have hfb : q.cur + q.s + q.t ≤ L ∧ q.cnt ≤ L ∧ q.sum ≤ L := by
          have := fold_bound w p0
          rw [hq_def]; simp only [p0] at this ⊢; omega
        obtain ⟨hfb1, hfb2, hfb3⟩ := hfb
        have hts : q.t * q.s ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
        by_cases hokW : q.ok
        · have hVT : VT (fun k => (st bB (tpR q) k).head?) = true := by
            rw [VT_eq bB hbB_clean q]; simp [hokW]
          obtain ⟨P, hPv, hPw⟩ := parse_ok w hokW
          have hpc := parse_code P hPv
          rw [← hPw, ← hq_def] at hpc
          obtain ⟨-, hqs, hqt⟩ := hpc
          obtain ⟨S3, hP3, hS3⟩ := run_phase3 P y L bB hbB_clean hbB_0 hbB_1 hbB_16
            (hPw ▸ hbB_14) hbB_15 q hokW hqs hqt (hPw ▸ hw_len) hy_len (by omega) (by omega)
          have hP2 := hCpW.seq (hLoopW.seq (hTP.seq (Run.branchT (q := noop) hVT hP3)))
          refine ⟨S3, _, hP1a.seq (Run.branchT (by simp [st, bA, hrem1, isSep])
            (hP1b.seq (Run.branchT (by simp [st, bB, hrem2]) hP2))), ?_, ?_⟩
          · rw [hS3]
            have hiff : (∃ assigns : List ℕ, y = unaryCode assigns ∧ assigns.length = 3 * P.s ∧
                (∀ a ∈ assigns, a < P.s) ∧ ∀ j < P.s, bucketSum j (List.ofFn P.entry) assigns = P.target) ↔
                s ∈ checkLang R := by
              rw [checkLang_iff_parsed]
              constructor
              · rintro ⟨assigns, hy_eq, halen, halt, hsum⟩
                exact ⟨w, y, P, assigns, hs_eq, hPv, hPw, hy_eq, halen, halt, hsum⟩
              · rintro ⟨w', y', P', assigns', hs', hPv', hPw', hy', halen', halt', hsum'⟩
                have h1 := takeInl_map_sep w' (y'.map (some ∘ Sum.inr))
                have hw_eq : w' = w := by
                  have := congrArg (fun l => (takeInl l).1) hs'
                  rw [h1] at this; exact this.symm
                have hy_eq' : y' = y := by
                  have hrem1' : rem1 = none :: y'.map (some ∘ Sum.inr) := by
                    rw [show rem1 = (takeInl s).2 from rfl, hs', h1]
                  rw [hrem1] at hrem1'
                  have := (List.cons.inj hrem1').2
                  have h2 := takeInr_map y'
                  have : y = (takeInr (y'.map (some ∘ Sum.inr))).1 := by rw [← this]
                  rw [h2] at this; exact this.symm
                subst hw_eq hy_eq'
                have hcode_eq : unaryCode (P.s :: P.target :: List.ofFn P.entry) =
                    unaryCode (P'.s :: P'.target :: List.ofFn P'.entry) := by
                  have : P.code = P'.code := hPw.symm.trans hPw'
                  simpa [ThreePartition.code] using this
                have hlist_eq := unaryCode_inj _ _ hcode_eq
                have hs_eq' : P.s = P'.s := (List.cons.inj hlist_eq).1
                have htail1 := (List.cons.inj hlist_eq).2
                have ht_eq' : P.target = P'.target := (List.cons.inj htail1).1
                have hes_eq' : List.ofFn P.entry = List.ofFn P'.entry := (List.cons.inj htail1).2
                refine ⟨assigns', hy', hs_eq' ▸ halen', fun a ha => hs_eq' ▸ halt' a ha, fun j hj => ?_⟩
                rw [ht_eq', hes_eq']; exact hsum' j (hs_eq' ▸ hj)
            unfold checkFun
            by_cases hmem : s ∈ checkLang R
            · simp [hmem, hiff.2 hmem]
            · simp [hmem, show ¬ _ from fun h => hmem (hiff.1 h)]
          · simp [hbB_14]
            have hL2 : w.length * (200 * L + 203) ≤ 200 * L ^ 2 + 203 * L :=
              (Nat.mul_le_mul_right _ hw_len).trans_eq (by ring)
            have hts' : q.t * q.s ≤ L ^ 2 := hts.trans_eq (by ring)
            have hcub : (L + 1) ^ 3 = L ^ 3 + 3 * L ^ 2 + 3 * L + 1 := by ring
            omega
        · have hVT : VT (fun k => (st bB (tpR q) k).head?) = false := by
            rw [VT_eq bB hbB_clean q]; simp [hokW]
          have hnot : s ∉ checkLang R := by
            rw [checkLang_iff_parsed]
            rintro ⟨w', y', P', -, hs', hPv', hPw', -⟩
            have h1 := takeInl_map_sep w' (y'.map (some ∘ Sum.inr))
            have hw_eq : w' = w := by
              have := congrArg (fun l => (takeInl l).1) hs'
              rw [h1] at this; exact this.symm
            subst hw_eq
            exact hokW (by rw [hq_def, hPw']; exact (parse_code P' hPv').1)
          have hP2 := hCpW.seq (hLoopW.seq (hTP.seq (Run.branchF (p := PHASE3) hVT (run_noop (st bB (tpR q))))))
          refine ⟨_, _, hP1a.seq (Run.branchT (by simp [st, bA, hrem1, isSep])
            (hP1b.seq (Run.branchT (by simp [st, bB, hrem2]) hP2))), ?_, ?_⟩
          · simp [st, hbB_1, tpR, toR, checkFun, hnot]
          · simp only [hbB_14, List.length_map]
            have hL2 : w.length * (200 * L + 203) ≤ 200 * L ^ 2 + 203 * L :=
              (Nat.mul_le_mul_right _ hw_len).trans_eq (by ring)
            have hts' : q.t * q.s ≤ L ^ 2 := hts.trans_eq (by ring)
            have hcub : (L + 1) ^ 3 = L ^ 3 + 3 * L ^ 2 + 3 * L + 1 := by ring
            omega

theorem checkFun_polytime : PolyTimeComputable checkFun := by
  obtain ⟨k, hk⟩ := polynomial_absorb 1000 3 1000
  refine stack_program_polytime VERIFY 0 1 checkFun k (fun s => ?_)
  obtain ⟨S, B, ⟨n, hn, he⟩, hS, hB⟩ := verify_run s
  exact ⟨S, n, by have := hk s.length; omega, he, hS⟩

theorem checkLang_mem_P : checkLang R ∈ CookPvsNP.P A := by
  refine mem_P_of_polyReducible (checkLang R) { l : List A | l ≠ [] } ?_ nonempty_mem_P
  refine ⟨checkFun, checkFun_polytime, fun s => ?_⟩
  unfold checkFun
  by_cases h : s ∈ checkLang R <;> simp [h]

/-! ### Part 9: Certificate length bound and main theorem -/

theorem len_unaryCode_le (ns : List ℕ) (M : ℕ) (hM : ∀ a ∈ ns, a + 1 ≤ M) :
    (unaryCode ns).length ≤ ns.length * M := by
  induction ns with
  | nil => simp [unaryCode_nil]
  | cons a ns ih =>
    rw [unaryCode_cons, List.length_append, List.length_replicate, List.length_cons,
      List.length_cons, add_one_mul]
    have h1 := hM a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => hM x (List.mem_cons_of_mem a hx))
    omega

theorem cert_len_le (P : ThreePartition) (assign : Fin (3 * P.s) → Fin P.s) :
    (unaryCode (List.ofFn (fun i => (assign i).val))).length ≤ P.code.length ^ 2 := by
  have h1 : (unaryCode (List.ofFn (fun i => (assign i).val))).length ≤ 3 * P.s * P.s := by
    have h := len_unaryCode_le (List.ofFn (fun i => (assign i).val)) P.s (fun a ha => by
      rw [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact (assign i).isLt)
    simpa [List.length_ofFn] using h
  have h2 : 4 * P.s + 2 ≤ P.code.length := by
    rw [ThreePartition.code]
    simp only [List.cons_append, List.nil_append, unaryCode_cons, List.length_append,
      List.length_replicate, List.length_cons]
    have h3 : (List.ofFn P.entry).length ≤ (unaryCode (List.ofFn P.entry)).length :=
      len_le_len_unaryCode _
    simp only [List.length_ofFn] at h3
    omega
  nlinarith

end ThreePartInNPPf

open TetrisHard.Rows in
theorem solution : threePartitionLanguage ∈ CookPvsNP.NP Bool := by
  refine ⟨Bool, inferInstance, inferInstance, ThreePartInNPPf.R, 2,
    ThreePartInNPPf.checkLang_mem_P, fun w => ?_⟩
  constructor
  · rintro ⟨P, hV, ⟨assign, hA⟩, rfl⟩
    exact ⟨unaryCode (List.ofFn (fun i => (assign i).val)),
      ThreePartInNPPf.cert_len_le P assign, P, assign, hV, hA, rfl, rfl⟩
  · rintro ⟨y, -, P, assign, hV, hA, rfl, -⟩
    exact ⟨P, hV, ⟨assign, hA⟩, rfl⟩
