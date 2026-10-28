-- Prove2me | solution 2 for SyncPrefix.Huffman.scAutomaton_encode_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:36:53.426352+00:00
-- url     : https://prove2.me/submissions/16594ed4-53d6-4ce5-841a-2e5f7bbe5128

import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Definitions.Def_SyncPrefix_Huffman_Constructions
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_consume
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_bounded_loop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open SyncPrefix.Huffman SetCoverThreshold.SetCover CookPvsNP

namespace ScAutomatonEncodePolyTime

abbrev Sym := Option Bool

inductive SKey where
  | ki
  | ko
  | outRev
  | P
  | PP
  | M
  | Qrem
  | Q
  | J
  | Jrem
  | Irem
  | W
  | Msc
  | Jsc
  | sc
  deriving DecidableEq

instance : Fintype SKey where
  elems := {.ki, .ko, .outRev, .P, .PP, .M, .Qrem, .Q, .J, .Jrem, .Irem, .W, .Msc, .Jsc, .sc}
  complete x := by cases x <;> decide

abbrev Prog := StackProg SKey Sym
abbrev Store := SKey → List Sym

lemma exec_congr {p : Prog} {s t t' : Store} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

lemma exec_seq_le {p q : Prog} {s t u : Store} {B1 B2 : ℕ}
    (h1 : ∃ c1 ≤ B1, p.Exec s t c1) (h2 : ∃ c2 ≤ B2, q.Exec t u c2) :
    ∃ c ≤ B1 + 1 + B2, (p.seq q).Exec s u c := by
  rcases h1 with ⟨c1, hc1, e1⟩
  rcases h2 with ⟨c2, hc2, e2⟩
  exact ⟨c1 + 1 + c2, by omega, StackProg.Exec.seq e1 e2⟩

lemma exec_le_of_le {p : Prog} {s t : Store} {B B' : ℕ}
    (h : ∃ c ≤ B, p.Exec s t c) (hB : B ≤ B') :
    ∃ c ≤ B', p.Exec s t c := by
  rcases h with ⟨c, hc, e⟩
  exact ⟨c, le_trans hc hB, e⟩

lemma exec_branch_true_le (test : (SKey → Option Sym) → Bool) (p q : Prog)
    {s t : Store} {B : ℕ}
    (ht : test (fun k => (s k).head?) = true)
    (hp : ∃ c ≤ B, p.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hp with ⟨c, hc, ep⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchTrue ht ep⟩

lemma exec_branch_false_le (test : (SKey → Option Sym) → Bool) (p q : Prog)
    {s t : Store} {B : ℕ}
    (hf : test (fun k => (s k).head?) = false)
    (hq : ∃ c ≤ B, q.Exec s t c) :
    ∃ c ≤ B + 1, (StackProg.branch test p q).Exec s t c := by
  rcases hq with ⟨c, hc, eq⟩
  exact ⟨1 + c, by omega, StackProg.Exec.branchFalse hf eq⟩

lemma exec_bounded_loop (test : (SKey → Option Sym) → Bool) (p : Prog)
    (n : ℕ) (s : ℕ → Store) (B : ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, ∃ c ≤ B, p.Exec (s i) (s (i + 1)) c) :
    ∃ t ≤ n * (B + 2) + 1, (StackProg.loop test p).Exec (s 0) (s n) t := by
  classical
  let cost : ℕ → ℕ := fun i => if h : i < n then Classical.choose (hb i h) else 0
  refine stack_bounded_loop test p n s cost B hg he ?_ ?_
  · intro i hi
    dsimp [cost]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hb i hi)).2
  · intro i hi
    dsimp [cost]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hb i hi)).1

/-- Emit `List.replicate v (some true) ++ [none]` in reverse onto `.outRev`,
where `src` holds `List.replicate v (some true)`. -/
def emitUnary (src : SKey) : Prog :=
  .seq (copyProg src .outRev .sc) (pushProg .outRev none)

lemma replicate_append_none_rev (v : ℕ) (acc : List Sym) :
    none :: (List.replicate v (some true) ++ acc) =
      (List.replicate v (some true) ++ [none]).reverse ++ acc := by
  simp [List.reverse_append]

lemma exec_emitUnary (src : SKey) (hsd : src ≠ .outRev) (hst : src ≠ .sc)
    (s : Store) (v : ℕ) (hsrc : s src = List.replicate v (some true)) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 5,
      (emitUnary src).Exec s
        (Function.update s .outRev ((List.replicate v (some true) ++ [none]).reverse ++ s .outRev)) c := by
  have e1 := stack_copy src .outRev .sc hsd hst (by decide) s hsc
  set s1 := Function.update s .outRev (s src ++ s .outRev)
  have e2 := (stack_basic_macros .outRev s1).1 none
  refine ⟨(6 * (s src).length + 3) + 1 + 1, by simp [hsrc], ?_⟩
  refine exec_congr (StackProg.Exec.seq e1 e2) ?_
  funext k
  cases k <;> simp [s1, hsrc, List.reverse_append]

/-! ### Stage 1: Parse `p` leading `some true`s and pop separator -/

def leadOnes : List Sym → ℕ
  | some true :: xs => leadOnes xs + 1
  | _ => 0

lemma leadOnes_le : ∀ w : List Sym, leadOnes w ≤ w.length
  | [] => by simp [leadOnes]
  | none :: _ => by simp [leadOnes]
  | some false :: _ => by simp [leadOnes]
  | some true :: xs => by
    simp only [leadOnes, List.length_cons]
    have := leadOnes_le xs
    omega

lemma head?_drop_of_lt_leadOnes : ∀ (w : List Sym) (i : ℕ), i < leadOnes w →
    (w.drop i).head? = some (some true)
  | some true :: _, 0, _ => rfl
  | some true :: xs, i + 1, hi => by
    simp only [leadOnes] at hi
    exact head?_drop_of_lt_leadOnes xs i (by omega)
  | [], _, hi => by simp [leadOnes] at hi
  | none :: _, _, hi => by simp [leadOnes] at hi
  | some false :: _, _, hi => by simp [leadOnes] at hi

lemma head?_drop_leadOnes : ∀ w : List Sym,
    (w.drop (leadOnes w)).head? ≠ some (some true)
  | [] => by simp [leadOnes]
  | none :: _ => by simp [leadOnes]
  | some false :: _ => by simp [leadOnes]
  | some true :: xs => by
    simp only [leadOnes, List.drop_succ_cons]
    exact head?_drop_leadOnes xs

lemma tail_drop_eq_drop_succ (w : List Sym) (i : ℕ) :
    (w.drop i).tail = w.drop (i + 1) := by
  rw [← List.drop_one, List.drop_drop, add_comm]

def readPAct (_h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = .ki then .pop else if k = .P then .push (some true) else .keep

def readPLoop : Prog :=
  .loop (fun h => decide (h .ki = some (some true))) (.act readPAct)

def readPProg : Prog :=
  .seq readPLoop (popProg .ki)

def sReadP (w : List Sym) (i : ℕ) : Store := fun k =>
  if k = .ki then w.drop i
  else if k = .P then List.replicate i (some true)
  else []

def storeAfterStage1 (w : List Sym) : Store := fun k =>
  if k = .ki then (w.drop (leadOnes w)).tail
  else if k = .P then List.replicate (leadOnes w) (some true)
  else []

lemma exec_readPProg (w : List Sym) :
    ∃ c ≤ 3 * w.length + 3,
      readPProg.Exec (fun k => if k = .ki then w else []) (storeAfterStage1 w) c := by
  have hloop : ∃ c1 ≤ leadOnes w * 3 + 1,
      readPLoop.Exec (sReadP w 0) (sReadP w (leadOnes w)) c1 := by
    refine exec_bounded_loop (fun h => decide (h .ki = some (some true)))
      (.act readPAct) (leadOnes w) (sReadP w) 1 ?_ ?_ ?_
    · intro i hi
      simp only [sReadP, ↓reduceIte, decide_eq_true_eq]
      exact head?_drop_of_lt_leadOnes w i hi
    · simp only [sReadP, ↓reduceIte, decide_eq_false_iff_not]
      exact head?_drop_leadOnes w
    · intro i _
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act readPAct (sReadP w i)) ?_⟩
      funext k
      cases k <;> simp [StackProg.applyAct, readPAct, sReadP, StackAct.apply,
        tail_drop_eq_drop_succ, List.replicate_succ]
  have h0 : (fun k => if k = .ki then w else []) = sReadP w 0 := by
    funext k; cases k <;> rfl
  rw [h0]
  have hpop : ∃ c2 ≤ 1, (popProg .ki).Exec (sReadP w (leadOnes w)) (storeAfterStage1 w) c2 := by
    refine ⟨1, le_rfl, exec_congr (stack_basic_macros .ki (sReadP w (leadOnes w))).2.1 ?_⟩
    funext k
    cases k <;> simp [sReadP, storeAfterStage1]
  have hle := leadOnes_le w
  exact exec_le_of_le (exec_seq_le hloop hpop) (by omega)

/-! ### Stage 2: Count `none`s in `body` into `.M` -/

def countMAct (h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = .W then .pop
  else if k = .M then
    match h .W with
    | some none => .push (some true)
    | _ => .keep
  else .keep

def countMLoop : Prog :=
  .loop (fun h => (h .W).isSome) (.act countMAct)

def countMProg : Prog :=
  .seq (copyProg .ki .W .sc) countMLoop

def sCountM (p : ℕ) (body : List Sym) (i : ℕ) : Store := fun k =>
  if k = .ki then body
  else if k = .P then List.replicate p (some true)
  else if k = .W then body.drop i
  else if k = .M then List.replicate ((body.take i).count none) (some true)
  else []

def storeAfterStage2 (p : ℕ) (body : List Sym) : Store := fun k =>
  if k = .ki then body
  else if k = .P then List.replicate p (some true)
  else if k = .M then List.replicate (body.count none) (some true)
  else []

lemma drop_eq_getElem_cons {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

lemma take_succ_count_none (body : List Sym) (i : ℕ) (hi : i < body.length) :
    (body.take (i + 1)).count none =
      (body.take i).count none + (if body[i] = none then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.count_append]
  cases h : body[i] with
  | none => simp
  | some b => cases b <;> simp

lemma exec_countMProg (p : ℕ) (body : List Sym) (s : Store)
    (hs : s = fun k => if k = .ki then body else if k = .P then List.replicate p (some true) else []) :
    ∃ c ≤ 9 * body.length + 5,
      countMProg.Exec s (storeAfterStage2 p body) c := by
  have e1 : ∃ c1 ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s (sCountM p body 0) c1 := by
    have hc := stack_copy SKey.ki SKey.W SKey.sc (by decide) (by decide) (by decide) s
      (by simp [hs])
    refine ⟨6 * (s .ki).length + 3, by simp [hs], exec_congr hc ?_⟩
    funext k
    cases k <;> simp [hs, sCountM]
  have e2 : ∃ c2 ≤ body.length * 3 + 1,
      countMLoop.Exec (sCountM p body 0) (storeAfterStage2 p body) c2 := by
    have hloop := exec_bounded_loop (fun h => (h .W).isSome) (.act countMAct)
      body.length (sCountM p body) 1
      (fun i hi => by
        simp only [sCountM, ↓reduceIte]
        rw [drop_eq_getElem_cons body i hi]
        rfl)
      (by simp [sCountM])
      (fun i hi => by
        refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act countMAct (sCountM p body i)) ?_⟩
        have hcnt := take_succ_count_none body i hi
        funext k
        cases k <;> simp [StackProg.applyAct, countMAct, sCountM, StackAct.apply,
          List.getElem?_eq_getElem hi, hcnt]
        · cases hbi : body[i] with
          | none => simp [List.replicate_succ]
          | some b => cases b <;> simp)
    rcases hloop with ⟨c2, hc2, eloop⟩
    refine ⟨c2, hc2, exec_congr eloop ?_⟩
    funext k
    cases k <;> simp [sCountM, storeAfterStage2]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

/-! ### Stage 3: Initialize `PP`, `Qrem`, `Jrem`, `Irem` and emit headers -/

def repPorts : Fin 4 ↪ SKey where
  toFun
    | ⟨0, _⟩ => .P
    | ⟨1, _⟩ => .PP
    | ⟨2, _⟩ => .Jsc
    | ⟨_ + 3, _⟩ => .sc
  inj' := by decide

def initCountersProg : Prog :=
  .seq (copyProg .P .Jsc .sc)
    (.seq (repeatCopyProg repPorts)
      (.seq (copyProg .PP .Qrem .sc)
        (.seq (pushProg .Qrem (some true))
          (.seq (emitUnary .Qrem)
            (.seq (emitUnary .M)
              (.seq (copyProg .P .Jrem .sc)
                (copyProg .P .Irem .sc)))))))

lemma flatten_replicate_replicate (a b : ℕ) (x : Sym) :
    (List.replicate a (List.replicate b x)).flatten = List.replicate (a * b) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, add_comm, List.replicate_add]

def headerRev (p m : ℕ) : List Sym :=
  (List.replicate m (some true) ++ [none]).reverse ++
    (List.replicate (p * p + 1) (some true) ++ [none]).reverse

def deltaVal (p : ℕ) (body : List Sym) (q a : ℕ) : ℕ :=
  if q < p * p then
    if q % p + 1 = p ∨ (body.drop (a * (p + 1) + q / p)).head? = some (some true) then
      p * p
    else q + 1
  else p * p

def encodeRowPart (p : ℕ) (body : List Sym) (q aBound : ℕ) : List Sym :=
  (List.range aBound).flatMap fun a =>
    List.replicate (deltaVal p body q a) (some true) ++ [none]

def encodeRow (p m : ℕ) (body : List Sym) (q : ℕ) : List Sym :=
  encodeRowPart p body q m

def encodeTable (p m : ℕ) (body : List Sym) (qBound : ℕ) : List Sym :=
  (List.range qBound).flatMap (encodeRow p m body)

lemma encodeRowPart_zero (p : ℕ) (body : List Sym) (q : ℕ) :
    encodeRowPart p body q 0 = [] := rfl

lemma encodeRowPart_succ (p : ℕ) (body : List Sym) (q a : ℕ) :
    (encodeRowPart p body q (a + 1)).reverse =
      (List.replicate (deltaVal p body q a) (some true) ++ [none]).reverse ++
        (encodeRowPart p body q a).reverse := by
  simp [encodeRowPart, List.range_succ, List.reverse_append]

lemma encodeTable_zero (p m : ℕ) (body : List Sym) :
    encodeTable p m body 0 = [] := rfl

lemma encodeTable_succ (p m : ℕ) (body : List Sym) (q : ℕ) :
    (encodeTable p m body (q + 1)).reverse =
      (encodeRow p m body q).reverse ++ (encodeTable p m body q).reverse := by
  simp [encodeTable, List.range_succ, List.reverse_append]

def qStore (p m : ℕ) (body : List Sym) (q : ℕ) : Store := fun k =>
  match k with
  | .ki => body
  | .P => List.replicate p (some true)
  | .PP => List.replicate (p * p) (some true)
  | .M => List.replicate m (some true)
  | .Qrem => List.replicate (p * p + 1 - q) (some true)
  | .Q => List.replicate (min q (p * p)) (some true)
  | .J => List.replicate (min q (p * p) / p) (some true)
  | .Jrem => List.replicate (p - min q (p * p) / p) (some true)
  | .Irem => List.replicate (p - min q (p * p) % p) (some true)
  | .outRev => (encodeTable p m body q).reverse ++ headerRev p m
  | .ko | .W | .Msc | .Jsc | .sc => []

lemma exec_initCountersProg (p : ℕ) (body : List Sym) :
    let m := body.count none
    ∃ c ≤ 18 * p * p + 31 * p + 6 * m + 40,
      initCountersProg.Exec (storeAfterStage2 p body) (qStore p m body 0) c := by
  intro m
  set s0 := storeAfterStage2 p body
  have h1 := stack_copy SKey.P SKey.Jsc SKey.sc (by decide) (by decide) (by decide) s0 rfl
  set s1 := Function.update s0 .Jsc (s0 .P ++ s0 .Jsc)
  have e1 : ∃ c ≤ 6 * p + 3, (copyProg .P .Jsc .sc).Exec s0 s1 c :=
    ⟨6 * (s0 .P).length + 3, by simp [s0, storeAfterStage2], h1⟩
  have h2 := stack_repeat_copy repPorts s1 (by simp [s1, s0, storeAfterStage2, repPorts])
  set s2 := Function.update (Function.update s1 .Jsc []) .PP
    ((List.replicate (s1 .Jsc).length (s1 .P)).flatten ++ s1 .PP)
  have e2 : ∃ c ≤ (6 * p + 7) * p + 1, (repeatCopyProg repPorts).Exec s1 s2 c := by
    refine ⟨((6 * (s1 .P).length + 7) * (s1 .Jsc).length + 1), ?_, h2⟩
    simp [s1, s0, storeAfterStage2]
  have hs2_PP : s2 .PP = List.replicate (p * p) (some true) := by
    simp [s2, s1, s0, storeAfterStage2, flatten_replicate_replicate]
  have hs2_sc : s2 .sc = [] := by
    simp [s2, s1, s0, storeAfterStage2]
  have h3 := stack_copy SKey.PP SKey.Qrem SKey.sc (by decide) (by decide) (by decide) s2 hs2_sc
  set s3 := Function.update s2 .Qrem (s2 .PP ++ s2 .Qrem)
  have e3 : ∃ c ≤ 6 * (p * p) + 3, (copyProg .PP .Qrem .sc).Exec s2 s3 c :=
    ⟨6 * (s2 .PP).length + 3, by simp [hs2_PP], h3⟩
  have h4 := (stack_basic_macros SKey.Qrem s3).1 (some true)
  set s4 := Function.update s3 .Qrem (some true :: s3 .Qrem)
  have e4 : ∃ c ≤ 1, (pushProg .Qrem (some true)).Exec s3 s4 c := ⟨1, le_rfl, h4⟩
  have hs4_Qrem : s4 .Qrem = List.replicate (p * p + 1) (some true) := by
    simp [s4, s3, hs2_PP, s2, s1, s0, storeAfterStage2, List.replicate_succ]
  have hs4_sc : s4 .sc = [] := by
    simp [s4, s3, s2, s1, s0, storeAfterStage2]
  have e5 := exec_emitUnary .Qrem (by decide) (by decide) s4 (p * p + 1) hs4_Qrem hs4_sc
  set s5 := Function.update s4 .outRev
    ((List.replicate (p * p + 1) (some true) ++ [none]).reverse ++ s4 .outRev)
  have hs5_M : s5 .M = List.replicate m (some true) := by
    simp [s5, s4, s3, s2, s1, s0, storeAfterStage2, m]
  have hs5_sc : s5 .sc = [] := by
    simp [s5, s4, s3, s2, s1, s0, storeAfterStage2]
  have e6 := exec_emitUnary .M (by decide) (by decide) s5 m hs5_M hs5_sc
  set s6 := Function.update s5 .outRev
    ((List.replicate m (some true) ++ [none]).reverse ++ s5 .outRev)
  have hs6_P : s6 .P = List.replicate p (some true) := by
    simp [s6, s5, s4, s3, s2, s1, s0, storeAfterStage2]
  have hs6_sc : s6 .sc = [] := by
    simp [s6, s5, s4, s3, s2, s1, s0, storeAfterStage2]
  have h7 := stack_copy SKey.P SKey.Jrem SKey.sc (by decide) (by decide) (by decide) s6 hs6_sc
  set s7 := Function.update s6 .Jrem (s6 .P ++ s6 .Jrem)
  have e7 : ∃ c ≤ 6 * p + 3, (copyProg .P .Jrem .sc).Exec s6 s7 c :=
    ⟨6 * (s6 .P).length + 3, by simp [hs6_P], h7⟩
  have hs7_sc : s7 .sc = [] := by
    simp [s7, hs6_sc]
  have h8 := stack_copy SKey.P SKey.Irem SKey.sc (by decide) (by decide) (by decide) s7 hs7_sc
  set s8 := Function.update s7 .Irem (s7 .P ++ s7 .Irem)
  have e8 : ∃ c ≤ 6 * p + 3, (copyProg .P .Irem .sc).Exec s7 (qStore p m body 0) c := by
    refine ⟨6 * (s7 .P).length + 3, by simp [s7, hs6_P], exec_congr h8 ?_⟩
    funext k
    cases k <;> simp [s8, s7, s6, s5, s4, s3, hs2_PP, s2, s1, s0, storeAfterStage2,
      qStore, encodeTable, headerRev, m, List.replicate_succ]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4
    (exec_seq_le e5 (exec_seq_le e6 (exec_seq_le e7 e8))))))
  refine exec_le_of_le e_all ?_
  nlinarith

/-! ### Stage 4: Main nested loop over `q < p * p + 1` and `a < m` -/

def aTrueBodyProg : Prog :=
  .seq (popProg .Msc)
    (.seq (copyProg .J .Jsc .sc)
      (.seq (consumeProg .Jsc (fun k => decide (k = .W)))
        (.seq (.branch (fun h => (h .Irem).isNone || decide (h .W = some (some true)))
                (emitUnary .PP) (emitUnary .Q))
          (.seq (copyProg .Jrem .Jsc .sc)
            (.seq (consumeProg .Jsc (fun k => decide (k = .W)))
              (popProg .W))))))

def aTrueLoopProg : Prog :=
  .loop (fun h => (h .Msc).isSome) aTrueBodyProg

def qUpdatePosProg : Prog :=
  .branch (fun h => (h .Irem).isNone)
    (.seq (copyProg .P .Irem .sc)
      (.seq (pushProg .J (some true))
        (popProg .Jrem)))
    (popProg .sc)

def qTrueProg : Prog :=
  .seq (popProg .Irem)
    (.seq (pushProg .Q (some true))
      (.seq (copyProg .ki .W .sc)
        (.seq (copyProg .M .Msc .sc)
          (.seq aTrueLoopProg
            (.seq (clearProg .W)
              qUpdatePosProg)))))

def aFalseBodyProg : Prog :=
  .seq (popProg .Msc) (emitUnary .PP)

def aFalseLoopProg : Prog :=
  .loop (fun h => (h .Msc).isSome) aFalseBodyProg

def qFalseProg : Prog :=
  .seq (copyProg .M .Msc .sc) aFalseLoopProg

def qBodyProg : Prog :=
  .seq (popProg .Qrem)
    (.branch (fun h => (h .Qrem).isSome) qTrueProg qFalseProg)

def qLoopProg : Prog :=
  .loop (fun h => (h .Qrem).isSome) qBodyProg

def aTrueStore (p m : ℕ) (body : List Sym) (q a : ℕ) : Store := fun k =>
  match k with
  | .ki => body
  | .P => List.replicate p (some true)
  | .PP => List.replicate (p * p) (some true)
  | .M => List.replicate m (some true)
  | .Qrem => List.replicate (p * p - q) (some true)
  | .Q => List.replicate (q + 1) (some true)
  | .J => List.replicate (q / p) (some true)
  | .Jrem => List.replicate (p - q / p) (some true)
  | .Irem => List.replicate (p - 1 - q % p) (some true)
  | .W => body.drop (a * (p + 1))
  | .Msc => List.replicate (m - a) (some true)
  | .outRev =>
      (encodeRowPart p body q a).reverse ++
        (encodeTable p m body q).reverse ++ headerRev p m
  | .ko | .Jsc | .sc => []

lemma head?_replicate_isNone (n : ℕ) (x : Sym) :
    (List.replicate n x).head?.isNone = decide (n = 0) := by
  cases n <;> rfl

lemma head?_replicate_isSome (n : ℕ) (x : Sym) :
    (List.replicate n x).head?.isSome = decide (0 < n) := by
  cases n <;> rfl

lemma exec_aTrueBodyProg (p m : ℕ) (body : List Sym) (q a : ℕ)
    (hq : q < p * p) (_ha : a < m) :
    ∃ c ≤ 6 * p * p + 18 * p + 22,
      aTrueBodyProg.Exec (aTrueStore p m body q a) (aTrueStore p m body q (a + 1)) c := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hq
    · exact hp
  have hj_lt : q / p < p := Nat.div_lt_of_lt_mul hq
  have hmod_lt : q % p < p := Nat.mod_lt q hp
  set s0 := aTrueStore p m body q a
  have h1 := (stack_basic_macros SKey.Msc s0).2.1
  set s1 := Function.update s0 .Msc (s0 .Msc).tail
  have e1 : ∃ c ≤ 1, (popProg .Msc).Exec s0 s1 c := ⟨1, le_rfl, h1⟩
  have h2 := stack_copy SKey.J SKey.Jsc SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, s0, aTrueStore])
  set s2 := Function.update s1 .Jsc (s1 .J ++ s1 .Jsc)
  have e2 : ∃ c ≤ 6 * p + 3, (copyProg .J .Jsc .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .J).length + 3, ?_, h2⟩
    simp [s1, s0, aTrueStore]
    omega
  have h3 := stack_consume SKey.Jsc (fun k => decide (k = .W)) s2
  set s3 := consumeStore .Jsc (fun k => decide (k = .W)) s2
  have e3 : ∃ c ≤ 3 * p + 1, (consumeProg .Jsc (fun k => decide (k = .W))).Exec s2 s3 c := by
    refine ⟨3 * (s2 .Jsc).length + 1, ?_, h3⟩
    simp [s2, s1, s0, aTrueStore]
    omega
  have hs3_Irem : s3 .Irem = List.replicate (p - 1 - q % p) (some true) := by
    simp [s3, consumeStore, s2, s1, s0, aTrueStore]
  have hs3_W : s3 .W = body.drop (a * (p + 1) + q / p) := by
    simp [s3, consumeStore, s2, s1, s0, aTrueStore, List.drop_drop]
  have hs3_PP : s3 .PP = List.replicate (p * p) (some true) := by
    simp [s3, consumeStore, s2, s1, s0, aTrueStore]
  have hs3_Q : s3 .Q = List.replicate (q + 1) (some true) := by
    simp [s3, consumeStore, s2, s1, s0, aTrueStore]
  have hs3_sc : s3 .sc = [] := by
    simp [s3, consumeStore, s2, s1, s0, aTrueStore]
  set s4 := Function.update s3 .outRev
    ((List.replicate (deltaVal p body q a) (some true) ++ [none]).reverse ++ s3 .outRev)
  have e4 : ∃ c ≤ 6 * (p * p) + 6,
      (StackProg.branch (fun h => (h .Irem).isNone || decide (h .W = some (some true)))
        (emitUnary .PP) (emitUnary .Q)).Exec s3 s4 c := by
    by_cases hcond : q % p + 1 = p ∨ (body.drop (a * (p + 1) + q / p)).head? = some (some true)
    · have htest : ((fun h : SKey → Option Sym => (h .Irem).isNone || decide (h .W = some (some true)))
          (fun k => (s3 k).head?)) = true := by
        show ((s3 .Irem).head?.isNone || decide ((s3 .W).head? = some (some true))) = true
        simp only [hs3_Irem, hs3_W, head?_replicate_isNone, Bool.or_eq_true,
          decide_eq_true_eq]
        rcases hcond with hmod | hhead
        · exact Or.inl (by omega)
        · exact Or.inr hhead
      have hdelta : deltaVal p body q a = p * p := by
        unfold deltaVal
        rw [if_pos hq, if_pos hcond]
      have hem := exec_emitUnary .PP (by decide) (by decide) s3 (p * p) hs3_PP hs3_sc
      rw [← hdelta] at hem
      exact exec_le_of_le
        (exec_branch_true_le (fun h => (h .Irem).isNone || decide (h .W = some (some true)))
          (emitUnary .PP) (emitUnary .Q) htest hem)
        (by rw [hdelta])
    · have htest : ((fun h : SKey → Option Sym => (h .Irem).isNone || decide (h .W = some (some true)))
          (fun k => (s3 k).head?)) = false := by
        show ((s3 .Irem).head?.isNone || decide ((s3 .W).head? = some (some true))) = false
        simp only [hs3_Irem, hs3_W, head?_replicate_isNone, Bool.or_eq_false_iff,
          decide_eq_false_iff_not, not_or] at hcond ⊢
        exact ⟨by omega, hcond.2⟩
      have hdelta : deltaVal p body q a = q + 1 := by
        unfold deltaVal
        rw [if_pos hq, if_neg hcond]
      have hem := exec_emitUnary .Q (by decide) (by decide) s3 (q + 1) hs3_Q hs3_sc
      have hem' : ∃ c ≤ 6 * (p * p) + 5, (emitUnary .Q).Exec s3 s4 c := by
        rw [← hdelta] at hem
        exact exec_le_of_le hem (by omega)
      exact exec_le_of_le
        (exec_branch_false_le (fun h => (h .Irem).isNone || decide (h .W = some (some true)))
          (emitUnary .PP) (emitUnary .Q) htest hem')
        (by omega)
  have hs4_sc : s4 .sc = [] := by
    simp [s4, hs3_sc]
  have hs4_Jrem : s4 .Jrem = List.replicate (p - q / p) (some true) := by
    simp [s4, s3, consumeStore, s2, s1, s0, aTrueStore]
  have hs4_Jsc : s4 .Jsc = [] := by
    simp [s4, s3, consumeStore]
  have h5 := stack_copy SKey.Jrem SKey.Jsc SKey.sc (by decide) (by decide) (by decide) s4 hs4_sc
  set s5 := Function.update s4 .Jsc (s4 .Jrem ++ s4 .Jsc)
  have e5 : ∃ c ≤ 6 * p + 3, (copyProg .Jrem .Jsc .sc).Exec s4 s5 c := by
    refine ⟨6 * (s4 .Jrem).length + 3, ?_, h5⟩
    simp [hs4_Jrem]
  have h6 := stack_consume SKey.Jsc (fun k => decide (k = .W)) s5
  set s6 := consumeStore .Jsc (fun k => decide (k = .W)) s5
  have e6 : ∃ c ≤ 3 * p + 1, (consumeProg .Jsc (fun k => decide (k = .W))).Exec s5 s6 c := by
    refine ⟨3 * (s5 .Jsc).length + 1, ?_, h6⟩
    simp [s5, hs4_Jrem, hs4_Jsc]
  have h7 := (stack_basic_macros SKey.W s6).2.1
  have e7 : ∃ c ≤ 1, (popProg .W).Exec s6 (aTrueStore p m body q (a + 1)) c := by
    refine ⟨1, le_rfl, exec_congr h7 ?_⟩
    funext k
    cases k <;> simp [s6, consumeStore, s5, s4, s3, s2, s1, s0, aTrueStore,
      encodeRowPart_succ, tail_drop_eq_drop_succ, List.drop_drop]
    · congr 1; rw [Nat.add_one_mul]; omega
    · omega
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4
    (exec_seq_le e5 (exec_seq_le e6 e7)))))
  refine exec_le_of_le e_all ?_
  nlinarith

lemma div_succ_of_mod_succ_eq {q p : ℕ} (hp : 0 < p) (h : q % p + 1 = p) :
    (q + 1) / p = q / p + 1 ∧ (q + 1) % p = 0 := by
  have hdiv := Nat.div_add_mod q p
  have hmul : p * (q / p + 1) = p * (q / p) + p := by ring
  have hq1 : q + 1 = p * (q / p + 1) := by omega
  rw [hq1]
  exact ⟨Nat.mul_div_right (q / p + 1) hp, Nat.mul_mod_right p (q / p + 1)⟩

lemma div_succ_of_mod_succ_ne {q p : ℕ} (hp : 0 < p) (h : q % p + 1 ≠ p) :
    (q + 1) / p = q / p ∧ (q + 1) % p = q % p + 1 := by
  have hmod := Nat.mod_lt q hp
  have hdiv := Nat.div_add_mod q p
  have hq1 : q + 1 = (q % p + 1) + p * (q / p) := by omega
  constructor
  · rw [hq1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]
  · rw [hq1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma exec_qTrueProg (p m : ℕ) (body : List Sym) (q : ℕ) (hq : q < p * p) :
    let sInit := Function.update (qStore p m body q) .Qrem (List.replicate (p * p - q) (some true))
    ∃ c ≤ m * (6 * p * p + 18 * p + 24) + 9 * body.length + 6 * m + 12 * p + 26,
      qTrueProg.Exec sInit (qStore p m body (q + 1)) c := by
  intro sInit
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hq
    · exact hp
  have hmod_lt : q % p < p := Nat.mod_lt q hp
  have hmin_q : min q (p * p) = q := Nat.min_eq_left (le_of_lt hq)
  have hmin_q1 : min (q + 1) (p * p) = q + 1 := Nat.min_eq_left hq
  have h1 := (stack_basic_macros SKey.Irem sInit).2.1
  set s1 := Function.update sInit .Irem (sInit .Irem).tail
  have e1 : ∃ c ≤ 1, (popProg .Irem).Exec sInit s1 c := ⟨1, le_rfl, h1⟩
  have h2 := (stack_basic_macros SKey.Q s1).1 (some true)
  set s2 := Function.update s1 .Q (some true :: s1 .Q)
  have e2 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec s1 s2 c := ⟨1, le_rfl, h2⟩
  have h3 := stack_copy SKey.ki SKey.W SKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, sInit, qStore])
  set s3 := Function.update s2 .W (s2 .ki ++ s2 .W)
  have e3 : ∃ c ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .ki).length + 3, ?_, h3⟩
    simp [s2, s1, sInit, qStore]
  have h4 := stack_copy SKey.M SKey.Msc SKey.sc (by decide) (by decide) (by decide) s3
    (by simp [s3, s2, s1, sInit, qStore])
  have e4 : ∃ c ≤ 6 * m + 3, (copyProg .M .Msc .sc).Exec s3 (aTrueStore p m body q 0) c := by
    refine ⟨6 * (s3 .M).length + 3, by simp [s3, s2, s1, sInit, qStore],
      exec_congr h4 ?_⟩
    funext k
    cases k <;> simp [s3, s2, s1, sInit, qStore, aTrueStore,
      hmin_q, List.replicate_succ, encodeRowPart_zero, Nat.sub_sub]
    · omega
  have e5 : ∃ c ≤ m * (6 * p * p + 18 * p + 24) + 1,
      aTrueLoopProg.Exec (aTrueStore p m body q 0) (aTrueStore p m body q m) c := by
    refine exec_bounded_loop (fun h => (h .Msc).isSome) aTrueBodyProg m
      (aTrueStore p m body q) (6 * p * p + 18 * p + 22) ?_ ?_ ?_
    · intro a ha
      simp [aTrueStore, head?_replicate_isSome, Nat.sub_pos_of_lt ha]
    · simp [aTrueStore]
    · intro a ha
      exact exec_aTrueBodyProg p m body q a hq ha
  set s5 := aTrueStore p m body q m
  have h6 := (stack_basic_macros SKey.W s5).2.2
  set s6 := Function.update s5 .W []
  have e6 : ∃ c ≤ 3 * body.length + 1, (clearProg .W).Exec s5 s6 c := by
    refine ⟨3 * (s5 .W).length + 1, ?_, h6⟩
    simp [s5, aTrueStore]
  have e7 : ∃ c ≤ 6 * p + 8, qUpdatePosProg.Exec s6 (qStore p m body (q + 1)) c := by
    by_cases hmod : q % p + 1 = p
    · obtain ⟨hdiv1, hmod1⟩ := div_succ_of_mod_succ_eq hp hmod
      have htest : (fun h : SKey → Option Sym => (h .Irem).isNone) (fun k => (s6 k).head?) = true := by
        show (s6 .Irem).head?.isNone = true
        simp [s6, s5, aTrueStore, head?_replicate_isNone]
        omega
      have hc1 := stack_copy SKey.P SKey.Irem SKey.sc (by decide) (by decide) (by decide) s6
        (by simp [s6, s5, aTrueStore])
      set u1 := Function.update s6 .Irem (s6 .P ++ s6 .Irem)
      have eu1 : ∃ c ≤ 6 * p + 3, (copyProg .P .Irem .sc).Exec s6 u1 c :=
        ⟨6 * (s6 .P).length + 3, by simp [s6, s5, aTrueStore], hc1⟩
      have hc2 := (stack_basic_macros SKey.J u1).1 (some true)
      set u2 := Function.update u1 .J (some true :: u1 .J)
      have eu2 : ∃ c ≤ 1, (pushProg .J (some true)).Exec u1 u2 c := ⟨1, le_rfl, hc2⟩
      have hc3 := (stack_basic_macros SKey.Jrem u2).2.1
      have eu3 : ∃ c ≤ 1, (popProg .Jrem).Exec u2 (qStore p m body (q + 1)) c := by
        refine ⟨1, le_rfl, exec_congr hc3 ?_⟩
        have hsub : p - 1 - q % p = 0 := by omega
        funext k
        cases k <;> simp [u2, u1, s6, s5, aTrueStore, qStore,
          hmin_q1, hdiv1, hmod1, hsub, List.replicate_succ, encodeTable_succ, encodeRow,
          Nat.sub_sub]
      exact exec_le_of_le
        (exec_branch_true_le (fun h => (h .Irem).isNone) _ (popProg .sc) htest
          (exec_seq_le eu1 (exec_seq_le eu2 eu3)))
        (by omega)
    · obtain ⟨hdiv1, hmod1⟩ := div_succ_of_mod_succ_ne hp hmod
      have htest : (fun h : SKey → Option Sym => (h .Irem).isNone) (fun k => (s6 k).head?) = false := by
        show (s6 .Irem).head?.isNone = false
        simp [s6, s5, aTrueStore, head?_replicate_isNone]
        omega
      have hc1 := (stack_basic_macros SKey.sc s6).2.1
      have eu1 : ∃ c ≤ 6 * p + 7, (popProg .sc).Exec s6 (qStore p m body (q + 1)) c := by
        refine ⟨1, by omega, exec_congr hc1 ?_⟩
        funext k
        cases k <;> simp [s6, s5, aTrueStore, qStore,
          hmin_q1, hdiv1, hmod1, encodeTable_succ, encodeRow, Nat.sub_sub]
        · omega
      exact exec_le_of_le
        (exec_branch_false_le (fun h => (h .Irem).isNone) _ (popProg .sc) htest eu1)
        (by omega)
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4
    (exec_seq_le e5 (exec_seq_le e6 e7)))))
  refine exec_le_of_le e_all ?_
  omega

def aFalseStore (p m : ℕ) (body : List Sym) (a : ℕ) : Store := fun k =>
  match k with
  | .ki => body
  | .P => List.replicate p (some true)
  | .PP => List.replicate (p * p) (some true)
  | .M => List.replicate m (some true)
  | .Qrem => []
  | .Q => List.replicate (p * p) (some true)
  | .J => List.replicate ((p * p) / p) (some true)
  | .Jrem => List.replicate (p - (p * p) / p) (some true)
  | .Irem => List.replicate (p - (p * p) % p) (some true)
  | .Msc => List.replicate (m - a) (some true)
  | .outRev =>
      (encodeRowPart p body (p * p) a).reverse ++
        (encodeTable p m body (p * p)).reverse ++ headerRev p m
  | .ko | .W | .Jsc | .sc => []

lemma exec_qFalseProg (p m : ℕ) (body : List Sym) :
    let sInit := Function.update (qStore p m body (p * p)) .Qrem []
    ∃ c ≤ m * (6 * p * p + 9) + 6 * m + 5,
      qFalseProg.Exec sInit (qStore p m body (p * p + 1)) c := by
  intro sInit
  have h1 := stack_copy SKey.M SKey.Msc SKey.sc (by decide) (by decide) (by decide) sInit
    (by simp [sInit, qStore])
  have e1 : ∃ c ≤ 6 * m + 3, (copyProg .M .Msc .sc).Exec sInit (aFalseStore p m body 0) c := by
    refine ⟨6 * (sInit .M).length + 3, by simp [sInit, qStore],
      exec_congr h1 ?_⟩
    funext k
    cases k <;> simp [sInit, qStore, aFalseStore, encodeRowPart_zero]
  have e2 : ∃ c ≤ m * (6 * p * p + 9) + 1,
      aFalseLoopProg.Exec (aFalseStore p m body 0) (qStore p m body (p * p + 1)) c := by
    have hloop := exec_bounded_loop (fun h => (h .Msc).isSome) aFalseBodyProg m
      (aFalseStore p m body) (6 * p * p + 7)
      (fun a ha => by simp [aFalseStore, head?_replicate_isSome, Nat.sub_pos_of_lt ha])
      (by simp [aFalseStore])
      (fun a ha => by
        set s0 := aFalseStore p m body a
        have hp1 := (stack_basic_macros SKey.Msc s0).2.1
        set s1 := Function.update s0 .Msc (s0 .Msc).tail
        have ep1 : ∃ c ≤ 1, (popProg .Msc).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
        have hs1_PP : s1 .PP = List.replicate (p * p) (some true) := by
          simp [s1, s0, aFalseStore]
        have hs1_sc : s1 .sc = [] := by
          simp [s1, s0, aFalseStore]
        have ep2 := exec_emitUnary .PP (by decide) (by decide) s1 (p * p) hs1_PP hs1_sc
        have hdelta : deltaVal p body (p * p) a = p * p := by simp [deltaVal]
        have ep2' : ∃ c ≤ 6 * (p * p) + 5, (emitUnary .PP).Exec s1 (aFalseStore p m body (a + 1)) c := by
          rcases ep2 with ⟨c2, hc2, ec2⟩
          refine ⟨c2, hc2, exec_congr ec2 ?_⟩
          funext k
          cases k <;> simp [s1, s0, aFalseStore, encodeRowPart_succ, hdelta, Nat.sub_sub]
        exact exec_le_of_le (exec_seq_le ep1 ep2') (by nlinarith))
    rcases hloop with ⟨c2, hc2, eloop⟩
    refine ⟨c2, hc2, exec_congr eloop ?_⟩
    funext k
    cases k <;> simp [aFalseStore, qStore, encodeTable_succ, encodeRow]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

lemma exec_qLoopProg (p m : ℕ) (body : List Sym) :
    let B := m * (6 * p * p + 18 * p + 24) + 9 * body.length + 6 * m + 12 * p + 29
    ∃ c ≤ (p * p + 1) * (B + 2) + 1,
      qLoopProg.Exec (qStore p m body 0) (qStore p m body (p * p + 1)) c := by
  intro B
  refine exec_bounded_loop (fun h => (h .Qrem).isSome) qBodyProg (p * p + 1)
    (qStore p m body) B ?_ ?_ ?_
  · intro q hq
    simp [qStore, head?_replicate_isSome, Nat.sub_pos_of_lt hq]
  · simp [qStore]
  · intro q hq
    have h1 := (stack_basic_macros SKey.Qrem (qStore p m body q)).2.1
    set s1 := Function.update (qStore p m body q) .Qrem (List.replicate (p * p - q) (some true))
    have e1 : ∃ c ≤ 1, (popProg .Qrem).Exec (qStore p m body q) s1 c := by
      refine ⟨1, le_rfl, exec_congr h1 ?_⟩
      funext k
      cases k <;> simp [s1, qStore, Nat.sub_sub]
    by_cases hq_lt : q < p * p
    · have htest : (fun h : SKey → Option Sym => (h .Qrem).isSome) (fun k => (s1 k).head?) = true := by
        show (s1 .Qrem).head?.isSome = true
        simp [s1, head?_replicate_isSome, Nat.sub_pos_of_lt hq_lt]
      have e2 := exec_branch_true_le (fun h => (h .Qrem).isSome) qTrueProg qFalseProg htest
        (exec_qTrueProg p m body q hq_lt)
      exact exec_le_of_le (exec_seq_le e1 e2) (by dsimp [B]; omega)
    · have hq_eq : q = p * p := by omega
      subst hq_eq
      have htest : (fun h : SKey → Option Sym => (h .Qrem).isSome) (fun k => (s1 k).head?) = false := by
        show (s1 .Qrem).head?.isSome = false
        simp [s1]
      have hs1_eq : s1 = Function.update (qStore p m body (p * p)) .Qrem [] := by
        funext k; simp [s1]
      rw [hs1_eq] at e1 htest
      have e2 := exec_branch_false_le (fun h => (h .Qrem).isSome) qTrueProg qFalseProg htest
        (exec_qFalseProg p m body)
      refine exec_le_of_le (exec_seq_le e1 e2) ?_
      dsimp [B]
      nlinarith

/-! ### Stage 5: Transfer `.outRev` to `.ko` and assemble `mainProg` -/

def mainProg : Prog :=
  .seq readPProg
    (.seq countMProg
      (.seq initCountersProg
        (.seq qLoopProg
          (transferProg .outRev (fun k => decide (k = .ko))))))

def f_sc (w : List Sym) : List Sym :=
  let p := leadOnes w
  let body := (w.drop p).tail
  let m := body.count none
  (headerRev p m).reverse ++ encodeTable p m body (p * p + 1)

lemma length_encodeRow (p m : ℕ) (body : List Sym) (q : ℕ) :
    (encodeRow p m body q).length ≤ m * (p * p + 2) := by
  unfold encodeRow encodeRowPart
  have h1 : ∀ a ∈ List.range m,
      (List.replicate (deltaVal p body q a) (some true) ++ [none]).length ≤ p * p + 2 := by
    intro a _
    simp only [List.length_append, List.length_replicate, List.length_singleton, deltaVal]
    split_ifs <;> omega
  calc ((List.range m).flatMap fun a =>
        List.replicate (deltaVal p body q a) (some true) ++ [none]).length
      = ((List.range m).map fun a =>
          (List.replicate (deltaVal p body q a) (some true) ++ [none]).length).sum := by
        rw [List.length_flatMap]
    _ ≤ ((List.range m).map fun _ => p * p + 2).sum := by
        exact List.sum_le_sum h1
    _ = m * (p * p + 2) := by simp

lemma length_encodeTable (p m : ℕ) (body : List Sym) (qBound : ℕ) :
    (encodeTable p m body qBound).length ≤ qBound * (m * (p * p + 2)) := by
  unfold encodeTable
  calc ((List.range qBound).flatMap (encodeRow p m body)).length
      = ((List.range qBound).map fun q => (encodeRow p m body q).length).sum := by
        rw [List.length_flatMap]
    _ ≤ ((List.range qBound).map fun _ => m * (p * p + 2)).sum := by
        exact List.sum_le_sum (fun q _ => length_encodeRow p m body q)
    _ = qBound * (m * (p * p + 2)) := by simp

lemma exec_mainProg (w : List Sym) :
    ∃ s c, c ≤ 350 * (w.length + 1) ^ 5 ∧
      mainProg.Exec (fun k => if k = .ki then w else []) s c ∧
      s .ko = f_sc w := by
  set L := w.length
  set p := leadOnes w
  set body := (w.drop p).tail
  set m := body.count none
  have hpL : p ≤ L := leadOnes_le w
  have hbodyL : body.length ≤ L := by
    simp [body, L]
  have hmL : m ≤ L := le_trans List.count_le_length hbodyL
  have e1 := exec_readPProg w
  have e2 := exec_countMProg p body (storeAfterStage1 w) rfl
  have e3 := exec_initCountersProg p body
  dsimp only at e3
  have e4 := exec_qLoopProg p m body
  dsimp only at e4
  set s4 := qStore p m body (p * p + 1)
  have h5 := stack_transfer SKey.outRev (fun k => decide (k = .ko)) s4
  set s5 := transferStore .outRev (fun k => decide (k = .ko)) s4
  have hout_len : (s4 .outRev).length ≤ (p * p + 1) * (m * (p * p + 2)) + m + p * p + 4 := by
    simp only [s4, qStore, headerRev, List.length_append, List.length_reverse,
      List.length_replicate, List.length_singleton]
    have htab := length_encodeTable p m body (p * p + 1)
    omega
  have e5 : ∃ c ≤ 3 * ((p * p + 1) * (m * (p * p + 2)) + m + p * p + 4) + 1,
      (transferProg .outRev (fun k => decide (k = .ko))).Exec s4 s5 c :=
    ⟨3 * (s4 .outRev).length + 1, by omega, h5⟩
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 e5)))
  rcases e_all with ⟨c, hc, ec⟩
  refine ⟨s5, c, ?_, ec, ?_⟩
  · set M := L + 1
    have h1M : 1 ≤ M := by omega
    have hpM : p ≤ M := by omega
    have hmM : m ≤ M := by omega
    have hbM : body.length ≤ M := by omega
    have hL_M : w.length ≤ M := by omega
    have hcnt_m : body.count none = m := rfl
    rw [hcnt_m] at hc
    set M2 := M * M
    set M3 := M * M2
    set M5 := M2 * M3
    have hM_M2 : M ≤ M2 := by simpa [M2] using Nat.le_mul_of_pos_left M h1M
    have h1_M2 : 1 ≤ M2 := le_trans h1M hM_M2
    have hM2_M3 : M2 ≤ M3 := by simpa [M3] using Nat.le_mul_of_pos_left M2 h1M
    have hM_M3 : M ≤ M3 := le_trans hM_M2 hM2_M3
    have h1_M3 : 1 ≤ M3 := le_trans h1_M2 hM2_M3
    have hM3_M5 : M3 ≤ M5 := by simpa [M5] using Nat.le_mul_of_pos_left M3 h1_M2
    have hM2_M5 : M2 ≤ M5 := le_trans hM2_M3 hM3_M5
    have hM_M5 : M ≤ M5 := le_trans hM_M3 hM3_M5
    have h1_M5 : 1 ≤ M5 := le_trans h1_M3 hM3_M5
    have hp2 : p * p ≤ M2 := Nat.mul_le_mul hpM hpM
    have hp6 : 6 * p * p = 6 * (p * p) := by ring
    have hp18 : 18 * p * p = 18 * (p * p) := by ring
    have h_in1 : 6 * p * p + 18 * p + 24 ≤ 48 * M2 := by omega
    have hm_in1 : m * (6 * p * p + 18 * p + 24) ≤ 48 * M3 := by
      have hmul := Nat.mul_le_mul hmM h_in1
      have heq : M * (48 * M2) = 48 * M3 := by dsimp [M3]; ring
      omega
    have hB_le : m * (6 * p * p + 18 * p + 24) + 9 * body.length + 6 * m + 12 * p + 29 + 2 ≤
        106 * M3 := by omega
    have hp2_1 : p * p + 1 ≤ 2 * M2 := by omega
    have h_loop_le : (p * p + 1) *
        (m * (6 * p * p + 18 * p + 24) + 9 * body.length + 6 * m + 12 * p + 29 + 2) ≤
        212 * M5 := by
      have hmul := Nat.mul_le_mul hp2_1 hB_le
      have heq : (2 * M2) * (106 * M3) = 212 * M5 := by dsimp [M5]; ring
      omega
    have hp2_2 : p * p + 2 ≤ 3 * M2 := by omega
    have hm_p2_2 : m * (p * p + 2) ≤ 3 * M3 := by
      have hmul := Nat.mul_le_mul hmM hp2_2
      have heq : M * (3 * M2) = 3 * M3 := by dsimp [M3]; ring
      omega
    have h_tab_le : (p * p + 1) * (m * (p * p + 2)) ≤ 6 * M5 := by
      have hmul := Nat.mul_le_mul hp2_1 hm_p2_2
      have heq : (2 * M2) * (3 * M3) = 6 * M5 := by dsimp [M5]; ring
      omega
    have hpow5 : M ^ 5 = M5 := by dsimp [M5, M3, M2]; ring
    rw [hpow5]
    omega
  · simp [s5, transferStore, s4, qStore, f_sc, p, body, m, List.reverse_append]

/-! ### Correctness on `I.encode`: `f_sc I.encode = (scAutomaton I).encode` -/

def scBlock {n : ℕ} (S : Finset (Fin n)) : List Sym :=
  List.ofFn (fun x : Fin n => some (decide (x ∈ S))) ++ [none]

lemma leadOnes_replicate_append (n : ℕ) (xs : List Sym) :
    leadOnes (List.replicate n (some true) ++ none :: xs) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, leadOnes, ih]

lemma drop_replicate_append (n : ℕ) (xs : List Sym) :
    ((List.replicate n (some true) ++ none :: xs).drop n).tail = xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, ih]

lemma count_none_ofFn_some {n : ℕ} (S : Finset (Fin n)) :
    (List.ofFn (fun x : Fin n => some (decide (x ∈ S)))).count none = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  rw [List.mem_ofFn] at hmem
  rcases hmem with ⟨i, hi⟩
  cases hi

lemma count_none_flatMap_scBlock {n : ℕ} :
    ∀ L : List (Finset (Fin n)), (L.flatMap scBlock).count none = L.length
  | [] => rfl
  | S :: L => by
    simp [List.flatMap_cons, scBlock, List.count_append, count_none_ofFn_some,
      count_none_flatMap_scBlock L]

lemma length_scBlock {n : ℕ} (S : Finset (Fin n)) :
    (scBlock S).length = n + 1 := by
  simp [scBlock]

lemma drop_flatMap_scBlock {n : ℕ} :
    ∀ (L : List (Finset (Fin n))) (a : ℕ),
      (L.flatMap scBlock).drop (a * (n + 1)) = (L.drop a).flatMap scBlock
  | L, 0 => by simp
  | [], a + 1 => by simp
  | S :: L, a + 1 => by
    have h1 : (scBlock S ++ L.flatMap scBlock).drop (n + 1) = L.flatMap scBlock := by
      rw [← length_scBlock S, List.drop_left]
    rw [List.flatMap_cons, Nat.succ_mul, add_comm (a * (n + 1)) (n + 1),
      ← List.drop_drop, h1, List.drop_succ_cons]
    exact drop_flatMap_scBlock L a

lemma head?_drop_scBlock {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (rest : List Sym) :
    ((scBlock S ++ rest).drop j.val).head? = some (some (decide (j ∈ S))) := by
  unfold scBlock
  rw [List.append_assoc]
  set v := List.ofFn (fun x : Fin n => some (decide (x ∈ S)))
  have hj : j.val < v.length := by simp [v, j.isLt]
  rw [List.head?_drop, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  simp [v]

lemma head?_drop_flatMap_scBlock {n : ℕ} (L : List (Finset (Fin n)))
    (a : Fin L.length) (j : Fin n) :
    ((L.flatMap scBlock).drop (a.val * (n + 1) + j.val)).head? =
      some (some (decide (j ∈ L.get a))) := by
  rw [← List.drop_drop, drop_flatMap_scBlock L a.val,
    drop_eq_getElem_cons L a.val a.isLt, List.flatMap_cons]
  exact head?_drop_scBlock (L.get a) j ((L.drop (a.val + 1)).flatMap scBlock)

lemma deltaVal_eq_scAutomaton_delta (I : SCInstance)
    (q : Fin (scAutomaton I).n) (a : Fin (scAutomaton I).k) :
    deltaVal I.n (I.sets.flatMap scBlock) q.val a.val = ((scAutomaton I).δ q a).val := by
  unfold deltaVal scAutomaton
  dsimp only
  by_cases hq : q.val < I.n * I.n
  · rw [if_pos hq, dif_pos hq]
    have hhead := head?_drop_flatMap_scBlock I.sets a ⟨q.val / I.n, Nat.div_lt_of_lt_mul hq⟩
    dsimp only at hhead
    rw [hhead]
    simp only [Option.some.injEq, decide_eq_true_eq]
    split_ifs <;> rfl
  · rw [if_neg hq, dif_neg hq]

lemma flatMap_finRange_eq_flatMap_range {α : Type} (n : ℕ) (g : ℕ → List α) :
    (List.finRange n).flatMap (fun x : Fin n => g x.val) = (List.range n).flatMap g := by
  have hmap : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [← List.flatMap_map, hmap]

lemma f_sc_encode (I : SCInstance) :
    f_sc I.encode = (scAutomaton I).encode := by
  unfold f_sc SCInstance.encode Automaton.encode
  have hp : leadOnes (List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock) = I.n :=
    leadOnes_replicate_append I.n (I.sets.flatMap scBlock)
  have hbody : ((List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock).drop I.n).tail =
      I.sets.flatMap scBlock :=
    drop_replicate_append I.n (I.sets.flatMap scBlock)
  have hm : (I.sets.flatMap scBlock).count none = I.sets.length :=
    count_none_flatMap_scBlock I.sets
  change (let p := leadOnes (List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock)
    let body := ((List.replicate I.n (some true) ++ none :: I.sets.flatMap scBlock).drop p).tail
    let m := body.count none
    (headerRev p m).reverse ++ encodeTable p m body (p * p + 1)) = _
  dsimp only
  rw [hp, hbody, hm]
  have htable : encodeTable I.n I.sets.length (I.sets.flatMap scBlock) (I.n * I.n + 1) =
      (List.finRange (scAutomaton I).n).flatMap fun q =>
        (List.finRange (scAutomaton I).k).flatMap fun a =>
          List.replicate ((scAutomaton I).δ q a).val (some true) ++ [none] := by
    have hrow : ∀ q : Fin (scAutomaton I).n,
        (List.finRange (scAutomaton I).k).flatMap (fun a =>
          List.replicate ((scAutomaton I).δ q a).val (some true) ++ [none]) =
          encodeRow I.n I.sets.length (I.sets.flatMap scBlock) q.val := by
      intro q
      simp_rw [← deltaVal_eq_scAutomaton_delta I q]
      exact flatMap_finRange_eq_flatMap_range I.sets.length
        (fun a => List.replicate (deltaVal I.n (I.sets.flatMap scBlock) q.val a) (some true) ++ [none])
    simp_rw [hrow]
    exact (flatMap_finRange_eq_flatMap_range (I.n * I.n + 1)
      (encodeRow I.n I.sets.length (I.sets.flatMap scBlock))).symm
  rw [htable]
  simp [headerRev, scAutomaton, List.reverse_append]

end ScAutomatonEncodePolyTime

theorem solution :
    ∃ f : List (Option Bool) → List (Option Bool), CookPvsNP.PolyTimeComputable f ∧
      ∀ I : SCInstance, f I.encode = (scAutomaton I).encode := by
  obtain ⟨k, hk⟩ := CookPvsNP.polynomial_absorb 350 5 0
  refine ⟨ScAutomatonEncodePolyTime.f_sc, ?_, ScAutomatonEncodePolyTime.f_sc_encode⟩
  refine CookPvsNP.stack_program_polytime
    ScAutomatonEncodePolyTime.mainProg .ki .ko ScAutomatonEncodePolyTime.f_sc k (fun w => ?_)
  obtain ⟨s, c, hc, he, ho⟩ := ScAutomatonEncodePolyTime.exec_mainProg w
  have hk_w := hk w.length
  exact ⟨s, c, by omega, he, ho⟩
