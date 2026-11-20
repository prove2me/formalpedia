-- Prove2me | solution 1 for TetrisHard.Rows.Padded.paddedNoBound_code_polytime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:01:34.793846+00:00
-- url     : https://prove2.me/submissions/027537ec-3c69-49b8-b77b-380ce91181c3

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction
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

namespace PaddedNoBoundPf

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

def Nval (padVal KVal stg s t : ℕ) : ℕ :=
  20 * (s * t) + 12 * t + 67 * s + (50 + 24 * padVal + 4 * KVal + stg)

theorem paddedNoBound_eq (P : ThreePartition) (hP : P.Valid) (he : Even P.target)
    (padVal KVal stg : ℕ) :
    TetrisHard.Rows.Padded.paddedNoBound P padVal KVal stg = Nval padVal KVal stg P.s P.target := by
  obtain ⟨m, hm⟩ := he
  unfold TetrisHard.Rows.Padded.paddedNoBound baseBoard basePieces baseHeight Nval
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

def progG (padVal KVal stg : ℕ) : StackProg K Bool :=
  .seq (pushProg 1 false) <| .seq (loopLead 2) <| .seq (popProg 0) <| .seq (loopLead 3) <|
  .seq (copyProg 2 4 6) <| .seq (repeatCopyProg e3546) <| .seq (pushN 4 20) <|
  .seq (repeatCopyProg e5146) <| .seq (pushN 4 12) <| .seq (repeatCopyProg e3146) <|
  .seq (pushN 4 67) <| .seq (repeatCopyProg e2146)
    (pushN 1 (50 + 24 * padVal + 4 * KVal + stg))

def gfun (padVal KVal stg : ℕ) (u : List Bool) : List Bool :=
  unaryCode [Nval padVal KVal stg (lead u) (lead (dropLead u).tail)]

theorem g_run (padVal KVal stg : ℕ) (u : List Bool) :
    ∃ S B, Run (progG padVal KVal stg) (st (fun j => if j = 0 then u else []) (fun _ => 0)) S B ∧
      S 1 = gfun padVal KVal stg u ∧
      B ≤ 300 * (u.length + 1) ^ 2 + 2 * (50 + 24 * padVal + 4 * KVal + stg) + 1000 := by
  refine ⟨_, _, Run.seq (run_pushB _ _ 1 false) <| Run.seq (run_loopLead 2 (by decide) u _ _ ?_ ?_) <|
    Run.seq (run_popB _ _ 0 ?_) <| Run.seq (run_loopLead 3 (by decide) _ _ _ rfl ?_) <|
    Run.seq (run_copy _ _ 2 4 6 (by decide) (by decide) (by decide) ?_ ?_ ?_) <|
    Run.seq (run_repeat _ _ e3546 ?_ ?_ ?_ ?_) <| Run.seq (run_pushN _ 4 20 _) <|
    Run.seq (run_repeat _ _ e5146 ?_ ?_ ?_ ?_) <| Run.seq (run_pushN _ 4 12 _) <|
    Run.seq (run_repeat _ _ e3146 ?_ ?_ ?_ ?_) <| Run.seq (run_pushN _ 4 67 _) <|
    Run.seq (run_repeat _ _ e2146 ?_ ?_ ?_ ?_)
      (run_pushN _ 1 (50 + 24 * padVal + 4 * KVal + stg) _), ?_, ?_⟩
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

theorem g_polytime (padVal KVal stg : ℕ) : PolyTimeComputable (gfun padVal KVal stg) := by
  obtain ⟨k, hk⟩ := polynomial_absorb 300 2 (2 * (50 + 24 * padVal + 4 * KVal + stg) + 1000)
  refine stack_program_polytime (progG padVal KVal stg) 0 1 (gfun padVal KVal stg) k (fun u => ?_)
  obtain ⟨S, B, ⟨n, hn, he⟩, hS, hB⟩ := g_run padVal KVal stg u
  exact ⟨S, n, by have := hk u.length; omega, he, hS⟩

theorem gfun_code (padVal KVal stg : ℕ) (P : ThreePartition) :
    gfun padVal KVal stg P.code = unaryCode [Nval padVal KVal stg P.s P.target] := by
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

end PaddedNoBoundPf

namespace TetrisHard.Rows.Padded

open TetrisHard.Rows

theorem paddedNoBound_code_polytime (pad K st : ℕ) :
    CookPvsNP.PolyTimeComputable
      (fun w : List Bool => unaryCode [paddedNoBound (normInstance w) pad K st]) := by
  have h := CookPvsNP.polyTimeComputable_comp _ _ PaddedNoBoundPf.normCode_polytime
    (PaddedNoBoundPf.g_polytime pad K st)
  convert h using 1
  funext w
  simp only [Function.comp]
  obtain ⟨hv, he⟩ := PaddedNoBoundPf.normInstance_valid w
  rw [PaddedNoBoundPf.gfun_code, PaddedNoBoundPf.paddedNoBound_eq _ hv he]

end TetrisHard.Rows.Padded

theorem solution (pad K st : ℕ) :
    CookPvsNP.PolyTimeComputable
      (fun w : List Bool => TetrisHard.Rows.unaryCode [TetrisHard.Rows.Padded.paddedNoBound (TetrisHard.Rows.normInstance w) pad K st]) :=
  TetrisHard.Rows.Padded.paddedNoBound_code_polytime pad K st
