-- Prove2me | solution 1 for SyncPrefix.Huffman.huffmanEncodeMap_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T01:37:56.374621+00:00
-- url     : https://prove2.me/submissions/6dfb0be2-e148-4ff9-8df6-4e50030a78d8

import Definitions.Def_SyncPrefix_Huffman_AutomatonCodec
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackRepeat
import Definitions.Def_CookPvsNP_StackCompare
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_consume
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_bounded_loop
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

-- Source: Solutions/HuffmanTotalEncodeCorrectness.lean
set_option autoImplicit false
namespace HuffmanTotalFormula
open SyncPrefix.Huffman
abbrev Sym := Option Bool
def encUnary (v : ℕ) : List Sym := List.replicate v (some true) ++ [none]
def leadOnes : List Sym → ℕ
  | some true :: xs => leadOnes xs + 1
  | _ => 0
def nextWord (w : List Sym) : List Sym := (w.drop (leadOnes w)).tail
def wordAt (w : List Sym) : ℕ → List Sym
  | 0 => w
  | i + 1 => nextWord (wordAt w i)
def valAt (w : List Sym) (i : ℕ) : ℕ := leadOnes (wordAt w i)
def headerRev (n k : ℕ) : List Sym :=
  (encUnary (k + 2)).reverse ++ (encUnary (2 * n)).reverse
def isSinkVal (k : ℕ) (body : List Sym) (q : ℕ) : Bool :=
  (List.range k).all fun a => decide (valAt body (q * k + a) = q)
def sinkValUpTo (k : ℕ) (body : List Sym) (q : ℕ) : ℕ :=
  ((List.range q).filter (isSinkVal k body)).headD 0
def extraVal (n k : ℕ) (body : List Sym) (q : ℕ) : ℕ :=
  if q = sinkValUpTo k body n then n else valAt body (q * k)
def phaseAMidPart (k : ℕ) (body : List Sym) (q : ℕ) (m : ℕ) : List Sym :=
  (List.range m).flatMap fun j => encUnary (valAt body (q * k + 1 + j))
def phaseARow (n k : ℕ) (body : List Sym) (q : ℕ) : List Sym :=
  encUnary (valAt body (q * k)) ++ phaseAMidPart k body q (k - 1) ++
    encUnary (extraVal n k body q) ++ encUnary (extraVal n k body q)
def phaseATable (n k : ℕ) (body : List Sym) (qBound : ℕ) : List Sym :=
  (List.range qBound).flatMap (phaseARow n k body)
def isSourceUpTo (body : List Sym) (f q m : ℕ) : Bool :=
  decide (q ≠ f) && (List.range m).all fun idx => decide (valAt body idx ≠ q)
def isSourceVal (n k : ℕ) (body : List Sym) (q : ℕ) : Bool :=
  isSourceUpTo body (sinkValUpTo k body n) q (n * k)
def sourceValsUpTo (n k : ℕ) (body : List Sym) (qBound : ℕ) : List ℕ :=
  (List.range qBound).filter (isSourceVal n k body)
def fkPart (f_val a : ℕ) : List Sym :=
  (List.range a).flatMap (fun _ => encUnary f_val)
def phaseC1ExtraVal (n f_val i : ℕ) : ℕ :=
  if i + 1 < n then n + (i + 1) else f_val
def phaseC1Row (n k f_val i : ℕ) : List Sym :=
  fkPart f_val k ++ encUnary (phaseC1ExtraVal n f_val i) ++ encUnary (phaseC1ExtraVal n f_val i)
def phaseC1Table (n k f_val iBound : ℕ) : List Sym :=
  (List.range iBound).flatMap (phaseC1Row n k f_val)
def phaseC2ExtraVal (n s_val i : ℕ) : ℕ :=
  if i + 1 < n then n + (i + 1) else s_val
def phaseC2Row (n k f_val : ℕ) (S_list : List ℕ) (d j : ℕ) : List Sym :=
  let s_val := S_list.getD j 0
  fkPart f_val k ++ encUnary s_val ++ encUnary (phaseC2ExtraVal n s_val (d + j))
def phaseC2Table (n k f_val : ℕ) (S_list : List ℕ) (d jBound : ℕ) : List Sym :=
  (List.range jBound).flatMap (phaseC2Row n k f_val S_list d)
def falseOutRev (n k : ℕ) : List Sym :=
  (encUnary n ++ encUnary (k + 2) ++
    (List.range n).flatMap (fun q => (List.range (k + 2)).flatMap (fun _ => encUnary q))).reverse
def trueOut (n k : ℕ) (body : List Sym) : List Sym :=
  let f_val := sinkValUpTo k body n
  let S_list := sourceValsUpTo n k body n
  let d := n - S_list.length
  (headerRev n k).reverse ++ phaseATable n k body n ++
    phaseC1Table n k f_val d ++ phaseC2Table n k f_val S_list d S_list.length
def f_huff (w : List Sym) : List Sym :=
  let n := valAt w 0
  let k := valAt w 1
  let body := wordAt w 2
  if 2 ≤ n ∧ 1 ≤ k then trueOut n k body else (falseOutRev n k).reverse

lemma leadOnes_replicate_append (n : ℕ) (xs : List Sym) :
    leadOnes (List.replicate n (some true) ++ none :: xs) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leadOnes, ih]

lemma nextWord_replicate_append (n : ℕ) (xs : List Sym) :
    nextWord (List.replicate n (some true) ++ none :: xs) = xs := by
  unfold nextWord
  rw [leadOnes_replicate_append]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

lemma drop_flatMap_encUnary :
    ∀ (L : List ℕ) (j : ℕ), j < L.length →
      (L.drop j).flatMap encUnary =
        List.replicate (L.getD j 0) (some true) ++ none :: (L.drop (j + 1)).flatMap encUnary
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: xs, 0, _ => by
    simp [encUnary]
  | _ :: xs, j + 1, hj => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
    simpa [List.drop_succ_cons] using drop_flatMap_encUnary xs j hj

def transVals (A : Automaton) : List ℕ :=
  (List.finRange A.n).flatMap fun q =>
    (List.finRange A.k).map fun a => (A.δ q a).val

def bodyA (A : Automaton) : List Sym :=
  (transVals A).flatMap encUnary

lemma encode_eq_bodyA (A : Automaton) :
    A.encode =
      List.replicate A.n (some true) ++ none ::
        (List.replicate A.k (some true) ++ none :: bodyA A) := by
  unfold Automaton.encode bodyA transVals
  simp only [encUnary, List.append_assoc, List.cons_append]
  congr 4
  induction (List.finRange A.n) with
  | nil => rfl
  | cons q qs ih =>
    simp [List.flatMap_cons, List.flatMap_append, List.flatMap_map, encUnary, ih]

lemma wordAt_zero_encode (A : Automaton) :
    wordAt A.encode 0 =
      List.replicate A.n (some true) ++ none ::
        (List.replicate A.k (some true) ++ none :: bodyA A) :=
  encode_eq_bodyA A

lemma wordAt_one_encode (A : Automaton) :
    wordAt A.encode 1 = List.replicate A.k (some true) ++ none :: bodyA A := by
  change nextWord (wordAt A.encode 0) = _
  rw [wordAt_zero_encode, nextWord_replicate_append]

lemma wordAt_two_encode (A : Automaton) :
    wordAt A.encode 2 = bodyA A := by
  change nextWord (wordAt A.encode 1) = _
  rw [wordAt_one_encode, nextWord_replicate_append]

lemma valAt_zero_encode (A : Automaton) :
    valAt A.encode 0 = A.n := by
  unfold valAt
  rw [wordAt_zero_encode, leadOnes_replicate_append]

lemma valAt_one_encode (A : Automaton) :
    valAt A.encode 1 = A.k := by
  unfold valAt
  rw [wordAt_one_encode, leadOnes_replicate_append]

lemma wordAt_succ_eq_wordAt_nextWord (w : List Sym) (idx : ℕ) :
    wordAt w (idx + 1) = wordAt (nextWord w) idx := by
  induction idx generalizing w with
  | zero => rfl
  | succ idx ih =>
    change nextWord (wordAt w (idx + 1)) = nextWord (wordAt (nextWord w) idx)
    rw [ih w]

lemma wordAt_flatMap_encUnary :
    ∀ (L : List ℕ) (idx : ℕ),
      wordAt (L.flatMap encUnary) idx = (L.drop idx).flatMap encUnary
  | L, 0 => by simp [wordAt]
  | [], idx + 1 => by
    rw [wordAt_succ_eq_wordAt_nextWord]
    have h0 : nextWord (([] : List ℕ).flatMap encUnary) = ([] : List ℕ).flatMap encUnary := rfl
    rw [h0, wordAt_flatMap_encUnary [] idx]
    simp
  | x :: xs, idx + 1 => by
    rw [wordAt_succ_eq_wordAt_nextWord, List.flatMap_cons]
    have h1 : encUnary x ++ xs.flatMap encUnary =
        List.replicate x (some true) ++ none :: xs.flatMap encUnary := by
      simp [encUnary]
    rw [h1, nextWord_replicate_append, List.drop_succ_cons]
    exact wordAt_flatMap_encUnary xs idx

lemma valAt_flatMap_encUnary (L : List ℕ) (idx : ℕ) (h : idx < L.length) :
    valAt (L.flatMap encUnary) idx = L.getD idx 0 := by
  unfold valAt
  rw [wordAt_flatMap_encUnary, drop_flatMap_encUnary L idx h, leadOnes_replicate_append]

lemma length_flatMap_const {α β : Type} (k : ℕ) (f : α → List β) (hf : ∀ x, (f x).length = k) :
    ∀ xs : List α, (xs.flatMap f).length = xs.length * k
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, hf x, length_flatMap_const k f hf xs,
      List.length_cons, Nat.succ_mul, add_comm]

lemma drop_flatMap_const {α β : Type} (k : ℕ) (f : α → List β) (hf : ∀ x, (f x).length = k) :
    ∀ (xs : List α) (q : ℕ), (xs.flatMap f).drop (q * k) = (xs.drop q).flatMap f
  | xs, 0 => by simp
  | [], q + 1 => by simp
  | x :: xs, q + 1 => by
    have h1 : (f x ++ xs.flatMap f).drop k = xs.flatMap f := by
      rw [← hf x, List.drop_left]
    rw [List.flatMap_cons, Nat.succ_mul, add_comm (q * k) k, ← List.drop_drop, h1,
      List.drop_succ_cons]
    exact drop_flatMap_const k f hf xs q

lemma length_transVals (A : Automaton) : (transVals A).length = A.n * A.k := by
  unfold transVals
  rw [length_flatMap_const A.k (fun q => (List.finRange A.k).map fun a => (A.δ q a).val)
    (fun _ => by simp), List.length_finRange]

lemma getD_zero_eq_getElem (L : List ℕ) (i : ℕ) (hi : i < L.length) :
    L.getD i 0 = L[i] := by
  induction L generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      exact ih i hi

lemma getD_drop_zero (L : List ℕ) (i : ℕ) :
    (L.drop i).getD 0 0 = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp [List.drop_succ_cons, ih i]

lemma drop_finRange_eq_cons {n : ℕ} (q : Fin n) :
    (List.finRange n).drop q.val = q :: (List.finRange n).drop (q.val + 1) := by
  have hlt : q.val < (List.finRange n).length := by simp [q.isLt]
  rw [List.drop_eq_getElem_cons hlt]
  simp

lemma getD_transVals (A : Automaton) (q : Fin A.n) (a : Fin A.k) :
    (transVals A).getD (q.val * A.k + a.val) 0 = (A.δ q a).val := by
  rw [← getD_drop_zero (transVals A) (q.val * A.k + a.val), ← List.drop_drop]
  unfold transVals
  rw [drop_flatMap_const A.k (fun q => (List.finRange A.k).map fun a => (A.δ q a).val)
    (fun _ => by simp) (List.finRange A.n) q.val, drop_finRange_eq_cons q, List.flatMap_cons]
  have hlen : a.val ≤ ((List.finRange A.k).map fun b => (A.δ q b).val).length := by
    simp [le_of_lt a.isLt]
  rw [List.drop_append_of_le_length hlen]
  have hmap_drop : ((List.finRange A.k).map fun b => (A.δ q b).val).drop a.val =
      (A.δ q a).val :: (((List.finRange A.k).drop (a.val + 1)).map fun b => (A.δ q b).val) := by
    rw [← List.map_drop, drop_finRange_eq_cons a, List.map_cons]
  rw [hmap_drop]
  rfl

lemma valAt_bodyA (A : Automaton) (q : Fin A.n) (a : Fin A.k) :
    valAt (bodyA A) (q.val * A.k + a.val) = (A.δ q a).val := by
  have hlt : q.val * A.k + a.val < (transVals A).length := by
    rw [length_transVals]
    calc q.val * A.k + a.val < q.val * A.k + A.k := Nat.add_lt_add_left a.isLt _
      _ = (q.val + 1) * A.k := by ring
      _ ≤ A.n * A.k := Nat.mul_le_mul_right A.k (Nat.succ_le_of_lt q.isLt)
  unfold bodyA
  rw [valAt_flatMap_encUnary (transVals A) (q.val * A.k + a.val) hlt, getD_transVals]

lemma finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

lemma getD_map_val_sourcesOf (A : Automaton) (hn : 0 < A.n) (j : ℕ)
    (hj : j < (sourcesOf A (sinkOf A hn)).length) :
    ((sourcesOf A (sinkOf A hn)).map Fin.val).getD j 0 =
      ((sourcesOf A (sinkOf A hn)).getD j (sinkOf A hn)).val := by
  have h1 : ((sourcesOf A (sinkOf A hn)).map Fin.val).getD j 0 =
      ((sourcesOf A (sinkOf A hn))[j]).val := by
    rw [getD_zero_eq_getElem _ j (by simp [hj]), List.getElem_map]
  have h2 : (sourcesOf A (sinkOf A hn)).getD j (sinkOf A hn) =
      (sourcesOf A (sinkOf A hn))[j] := by
    unfold List.getD
    rw [List.getElem?_eq_getElem hj]
    rfl
  rw [h1, h2]

lemma flatMap_finRange_eq_flatMap_range {α : Type} (n : ℕ) (g : ℕ → List α) :
    (List.finRange n).flatMap (fun x : Fin n => g x.val) = (List.range n).flatMap g := by
  rw [← List.flatMap_map, finRange_map_val]

lemma flatMap_range_add {α : Type} (a b : ℕ) (g : ℕ → List α) :
    (List.range (a + b)).flatMap g =
      (List.range a).flatMap g ++ (List.range b).flatMap (fun i => g (a + i)) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]


lemma isSinkVal_bodyA (A : Automaton) (q : Fin A.n) :
    isSinkVal A.k (bodyA A) q.val =
      (List.finRange A.k).all (fun a ↦ decide (A.δ q a = q)) := by
  unfold isSinkVal
  rw [← finRange_map_val A.k, List.all_map]
  congr 1
  funext a
  dsimp only [Function.comp_apply]
  rw [valAt_bodyA]
  simp only [Fin.ext_iff]

lemma sinkValUpTo_bodyA (A : Automaton) (hn : 0 < A.n) :
    sinkValUpTo A.k (bodyA A) A.n = (sinkOf A hn).val := by
  have hf : (List.range A.n).filter (isSinkVal A.k (bodyA A)) =
      ((List.finRange A.n).filter (fun q ↦
        (List.finRange A.k).all (fun a ↦ decide (A.δ q a = q)))).map Fin.val := by
    rw [← finRange_map_val A.n, List.filter_map]
    congr 1
    apply List.filter_congr
    intro q _
    exact isSinkVal_bodyA A q
  unfold sinkValUpTo sinkOf
  rw [hf]
  generalize ((List.finRange A.n).filter fun q ↦
    (List.finRange A.k).all fun a ↦ decide (A.δ q a = q)) = qs
  cases qs <;> rfl

lemma isSourceVal_bodyA (A : Automaton) (hn : 0 < A.n) (hk : 1 ≤ A.k)
    (q : Fin A.n) :
    isSourceVal A.n A.k (bodyA A) q.val =
      (decide (q ≠ sinkOf A hn) &&
        (List.finRange A.n).all fun p ↦
          (List.finRange A.k).all fun a ↦ decide (A.δ p a ≠ q)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isSourceVal, isSourceUpTo, sinkValUpTo_bodyA A hn, List.all_eq_true,
    List.mem_range, Bool.and_eq_true, List.mem_finRange, decide_eq_true_eq, true_imp_iff]
  constructor
  · rintro ⟨hne, hall⟩
    refine ⟨fun h ↦ hne (congrArg Fin.val h), fun p a hpa ↦ ?_⟩
    have hlt : p.val * A.k + a.val < A.n * A.k := by
      calc p.val * A.k + a.val < p.val * A.k + A.k := Nat.add_lt_add_left a.isLt _
        _ = (p.val + 1) * A.k := by ring
        _ ≤ A.n * A.k := Nat.mul_le_mul_right A.k (Nat.succ_le_of_lt p.isLt)
    have hval := valAt_bodyA A p a
    rw [hpa] at hval
    exact hall (p.val * A.k + a.val) hlt hval
  · rintro ⟨hne, hno⟩
    refine ⟨fun h ↦ hne (Fin.ext h), ?_⟩
    intro idx hidx
    have hk_pos : 0 < A.k := by omega
    have hidx_kn : idx < A.k * A.n := by rw [mul_comm]; exact hidx
    let p : Fin A.n := ⟨idx / A.k, Nat.div_lt_of_lt_mul hidx_kn⟩
    let a : Fin A.k := ⟨idx % A.k, Nat.mod_lt idx hk_pos⟩
    have hidx_eq : p.val * A.k + a.val = idx := by
      dsimp [p, a]
      rw [mul_comm, Nat.div_add_mod]
    rw [← hidx_eq, valAt_bodyA A p a]
    exact fun h ↦ hno p a (Fin.ext h)

lemma sourceValsUpTo_bodyA (A : Automaton) (hn : 0 < A.n) (hk : 1 ≤ A.k) :
    sourceValsUpTo A.n A.k (bodyA A) A.n = (sourcesOf A (sinkOf A hn)).map Fin.val := by
  unfold sourceValsUpTo sourcesOf
  rw [← finRange_map_val A.n, List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  exact isSourceVal_bodyA A hn hk q

lemma length_sourceValsUpTo_le (n k : ℕ) (body : List Sym) (qBound : ℕ) :
    (sourceValsUpTo n k body qBound).length ≤ qBound := by
  simpa only [sourceValsUpTo, List.length_range] using
    List.length_filter_le (isSourceVal n k body) (List.range qBound)


lemma phaseARow_bodyA (A : Automaton) (h : 2 ≤ A.n ∧ 1 ≤ A.k) (q₀ : Fin A.n) :
    phaseARow A.n A.k (bodyA A) q₀.val =
      (List.range (A.k + 2)).flatMap fun a =>
        if ha : a < A.k then
          encUnary (A.δ q₀ ⟨a, ha⟩).val
        else if q₀ = sinkOf A (by omega) then
          encUnary A.n
        else
          encUnary (A.δ q₀ ⟨0, by omega⟩).val := by
  have hn : 0 < A.n := by omega
  have hk : 1 ≤ A.k := h.2
  have hk_split : A.k + 2 = (1 + (A.k - 1)) + 2 := by omega
  rw [hk_split, flatMap_range_add (1 + (A.k - 1)) 2, flatMap_range_add 1 (A.k - 1)]
  have h0 : (List.range 1).flatMap (fun a =>
      if ha : a < A.k then encUnary (A.δ q₀ ⟨a, ha⟩).val
      else if q₀ = sinkOf A hn then encUnary A.n
      else encUnary (A.δ q₀ ⟨0, by omega⟩).val) =
      encUnary (valAt (bodyA A) (q₀.val * A.k)) := by
    have hval := valAt_bodyA A q₀ ⟨0, by omega⟩
    simp only [Nat.add_zero] at hval
    have hk0 : 0 < A.k := by omega
    simp [List.range_one, hk0, hval]
  have hmid : (List.range (A.k - 1)).flatMap (fun j =>
      if ha : 1 + j < A.k then encUnary (A.δ q₀ ⟨1 + j, ha⟩).val
      else if q₀ = sinkOf A hn then encUnary A.n
      else encUnary (A.δ q₀ ⟨0, by omega⟩).val) =
      phaseAMidPart A.k (bodyA A) q₀.val (A.k - 1) := by
    unfold phaseAMidPart
    refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    have ha : 1 + j < A.k := by omega
    rw [dif_pos ha]
    have hval := valAt_bodyA A q₀ ⟨1 + j, ha⟩
    have hidx : q₀.val * A.k + (1 + j) = q₀.val * A.k + 1 + j := by omega
    rw [← hval, hidx]
  have hextra : extraVal A.n A.k (bodyA A) q₀.val =
      if q₀ = sinkOf A hn then A.n else (A.δ q₀ ⟨0, by omega⟩).val := by
    unfold extraVal
    rw [sinkValUpTo_bodyA A hn]
    have hval := valAt_bodyA A q₀ ⟨0, by omega⟩
    simp only [Nat.add_zero] at hval
    by_cases hq : q₀ = sinkOf A hn
    · rw [if_pos (congrArg Fin.val hq), if_pos hq]
    · rw [if_neg (fun hv => hq (Fin.ext hv)), if_neg hq, hval]
  have h2 : (List.range 2).flatMap (fun i =>
      if ha : 1 + (A.k - 1) + i < A.k then encUnary (A.δ q₀ ⟨1 + (A.k - 1) + i, ha⟩).val
      else if q₀ = sinkOf A hn then encUnary A.n
      else encUnary (A.δ q₀ ⟨0, by omega⟩).val) =
      encUnary (extraVal A.n A.k (bodyA A) q₀.val) ++
        encUnary (extraVal A.n A.k (bodyA A) q₀.val) := by
    have hr2 : List.range 2 = [0, 1] := rfl
    have hna0 : ¬ (1 + (A.k - 1) + 0 < A.k) := by omega
    have hna1 : ¬ (1 + (A.k - 1) + 1 < A.k) := by omega
    rw [hr2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      dif_neg hna0, dif_neg hna1, hextra]
    split_ifs <;> rfl
  rw [h0, hmid, h2]
  simp [phaseARow, List.append_assoc]

lemma f_huff_encode (A : Automaton) :
    f_huff A.encode = (huffmanOfStronglyAcyclic A).encode := by
  unfold f_huff
  rw [valAt_zero_encode, valAt_one_encode, wordAt_two_encode]
  by_cases h : 2 ≤ A.n ∧ 1 ≤ A.k
  · have hn_pos : 0 < A.n := by omega
    rw [if_pos h]
    unfold trueOut
    have hf_eq : sinkValUpTo A.k (bodyA A) A.n = (sinkOf A hn_pos).val :=
      sinkValUpTo_bodyA A hn_pos
    have hS_eq : sourceValsUpTo A.n A.k (bodyA A) A.n =
        (sourcesOf A (sinkOf A hn_pos)).map Fin.val :=
      sourceValsUpTo_bodyA A hn_pos h.2
    set f := sinkOf A hn_pos
    set S := sourcesOf A f
    set d := A.n - S.length
    have hlen_S_le : S.length ≤ A.n := by
      have h := length_sourceValsUpTo_le A.n A.k (bodyA A) A.n
      simpa [hS_eq, S, f] using h
    have hd_add : d + S.length = A.n := Nat.sub_add_cancel hlen_S_le
    dsimp only
    rw [hf_eq, hS_eq]
    simp only [List.length_map]
    unfold huffmanOfStronglyAcyclic Automaton.encode
    rw [dif_pos h]
    dsimp only
    let gRow : ℕ → List Sym := fun q =>
      (List.range (A.k + 2)).flatMap fun a =>
        if hq : q < A.n then
          if ha : a < A.k then
            encUnary (A.δ ⟨q, hq⟩ ⟨a, ha⟩).val
          else if q = f.val then
            encUnary A.n
          else
            encUnary (A.δ ⟨q, hq⟩ ⟨0, by omega⟩).val
        else
          let i := q - A.n
          if a < A.k then
            encUnary f.val
          else if i < d then
            encUnary (phaseC1ExtraVal A.n f.val i)
          else
            let j := i - d
            let s_j := S.getD j f
            if a = A.k then
              encUnary s_j.val
            else
              encUnary (phaseC2ExtraVal A.n s_j.val i)
    have h_row_eq : ∀ q : Fin (2 * A.n),
        ((List.finRange (A.k + 2)).flatMap fun a =>
          List.replicate
            ((if hq : q.val < A.n then
                if ha : a.val < A.k then
                  ⟨(A.δ ⟨q.val, hq⟩ ⟨a.val, ha⟩).val, by omega⟩
                else if (⟨q.val, hq⟩ : Fin A.n) = f then
                  ⟨A.n, by omega⟩
                else
                  ⟨(A.δ ⟨q.val, hq⟩ ⟨0, by omega⟩).val, by omega⟩
              else
                let i := q.val - A.n
                if _ha : a.val < A.k then
                  ⟨f.val, by omega⟩
                else if i < d then
                  if _hnext : i + 1 < A.n then
                    ⟨A.n + (i + 1), by omega⟩
                  else
                    ⟨f.val, by omega⟩
                else
                  let j := i - d
                  let s_j := S.getD j f
                  if a.val = A.k then
                    ⟨s_j.val, by omega⟩
                  else if _hnext : i + 1 < A.n then
                    ⟨A.n + (i + 1), by omega⟩
                  else
                    ⟨s_j.val, by omega⟩ : Fin (2 * A.n)).val) (some true) ++ [none]) =
        gRow q.val := by
      intro q
      dsimp only [gRow]
      rw [← flatMap_finRange_eq_flatMap_range (A.k + 2)]
      refine List.flatMap_congr fun a _ => ?_
      by_cases hq : q.val < A.n
      · rw [dif_pos hq, dif_pos hq]
        by_cases ha : a.val < A.k
        · rw [dif_pos ha, dif_pos ha]; rfl
        · rw [dif_neg ha, dif_neg ha]
          by_cases hqf : (⟨q.val, hq⟩ : Fin A.n) = f
          · have hqf_val : q.val = f.val := congrArg Fin.val hqf
            rw [if_pos hqf, if_pos hqf_val]; rfl
          · have hqf_val : q.val ≠ f.val := fun hv => hqf (Fin.ext hv)
            rw [if_neg hqf, if_neg hqf_val]; rfl
      · rw [dif_neg hq, dif_neg hq]
        by_cases ha : a.val < A.k
        · rw [dif_pos ha, if_pos ha]; rfl
        · rw [dif_neg ha, if_neg ha]
          by_cases hi : q.val - A.n < d
          · rw [ if_pos hi, if_pos hi]
            unfold phaseC1ExtraVal
            split_ifs <;> rfl
          · rw [if_neg hi, if_neg hi]
            by_cases hak : a.val = A.k
            · rw [if_pos hak, if_pos hak]; rfl
            · rw [if_neg hak, if_neg hak]
              unfold phaseC2ExtraVal
              split_ifs <;> rfl
    have h_table_eq :
        ((List.finRange (2 * A.n)).flatMap fun q =>
          (List.finRange (A.k + 2)).flatMap fun a =>
            List.replicate
              ((if hq : q.val < A.n then
                  if ha : a.val < A.k then
                    ⟨(A.δ ⟨q.val, hq⟩ ⟨a.val, ha⟩).val, by omega⟩
                  else if (⟨q.val, hq⟩ : Fin A.n) = f then
                    ⟨A.n, by omega⟩
                  else
                    ⟨(A.δ ⟨q.val, hq⟩ ⟨0, by omega⟩).val, by omega⟩
                else
                  let i := q.val - A.n
                  if _ha : a.val < A.k then
                    ⟨f.val, by omega⟩
                  else if i < d then
                    if _hnext : i + 1 < A.n then
                      ⟨A.n + (i + 1), by omega⟩
                    else
                      ⟨f.val, by omega⟩
                  else
                    let j := i - d
                    let s_j := S.getD j f
                    if a.val = A.k then
                      ⟨s_j.val, by omega⟩
                    else if _hnext : i + 1 < A.n then
                      ⟨A.n + (i + 1), by omega⟩
                    else
                      ⟨s_j.val, by omega⟩ : Fin (2 * A.n)).val) (some true) ++ [none]) =
        (List.finRange (2 * A.n)).flatMap (fun q => gRow q.val) :=
      List.flatMap_congr fun q _ => h_row_eq q
    have h_range_split : (List.finRange (2 * A.n)).flatMap (fun q => gRow q.val) =
        (List.range A.n).flatMap gRow ++
          ((List.range d).flatMap (fun i => gRow (A.n + i)) ++
            (List.range S.length).flatMap (fun j => gRow (A.n + (d + j)))) := by
      rw [flatMap_finRange_eq_flatMap_range (2 * A.n) gRow,
        show 2 * A.n = A.n + (d + S.length) by omega,
        flatMap_range_add A.n (d + S.length) gRow,
        flatMap_range_add d S.length (fun i => gRow (A.n + i))]
    rw [h_table_eq, h_range_split]
    dsimp only [gRow]
    have h_partA : (List.range A.n).flatMap (fun q =>
        (List.range (A.k + 2)).flatMap fun a =>
          if hq : q < A.n then
            if ha : a < A.k then
              encUnary (A.δ ⟨q, hq⟩ ⟨a, ha⟩).val
            else if q = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨q, hq⟩ ⟨0, by omega⟩).val
          else
            let i := q - A.n
            if a < A.k then
              encUnary f.val
            else if i < d then
              encUnary (phaseC1ExtraVal A.n f.val i)
            else
              let j := i - d
              let s_j := S.getD j f
              if a = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i)) =
        phaseATable A.n A.k (bodyA A) A.n := by
      unfold phaseATable
      refine List.flatMap_congr fun q hq_mem => ?_
      rw [List.mem_range] at hq_mem
      have hrow := (phaseARow_bodyA A h ⟨q, hq_mem⟩).symm
      refine (List.flatMap_congr fun a _ => ?_).trans hrow
      rw [dif_pos hq_mem]
      by_cases ha : a < A.k
      · rw [dif_pos ha, dif_pos ha]
      · rw [dif_neg ha, dif_neg ha]
        by_cases hqf : (⟨q, hq_mem⟩ : Fin A.n) = f
        · have hqf_val : q = f.val := congrArg Fin.val hqf
          rw [if_pos hqf_val, if_pos hqf]
        · have hqf_val : q ≠ f.val := fun hv => hqf (Fin.ext hv)
          rw [if_neg hqf_val, if_neg hqf]
    have h_partC1 : (List.range d).flatMap (fun i =>
        (List.range (A.k + 2)).flatMap fun a =>
          if hq : A.n + i < A.n then
            if ha : a < A.k then
              encUnary (A.δ ⟨A.n + i, hq⟩ ⟨a, ha⟩).val
            else if A.n + i = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨A.n + i, hq⟩ ⟨0, by omega⟩).val
          else
            let i' := A.n + i - A.n
            if a < A.k then
              encUnary f.val
            else if i' < d then
              encUnary (phaseC1ExtraVal A.n f.val i')
            else
              let j := i' - d
              let s_j := S.getD j f
              if a = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i')) =
        phaseC1Table A.n A.k f.val d := by
      unfold phaseC1Table
      refine List.flatMap_congr fun i hi_mem => ?_
      rw [List.mem_range] at hi_mem
      have hnq : ¬ (A.n + i < A.n) := by omega
      have hsub : A.n + i - A.n = i := by omega
      rw [flatMap_range_add A.k 2]
      have hfk : (List.range A.k).flatMap (fun a =>
          if hq : A.n + i < A.n then
            if ha : a < A.k then
              encUnary (A.δ ⟨A.n + i, hq⟩ ⟨a, ha⟩).val
            else if A.n + i = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨A.n + i, hq⟩ ⟨0, by omega⟩).val
          else
            let i' := A.n + i - A.n
            if a < A.k then
              encUnary f.val
            else if i' < d then
              encUnary (phaseC1ExtraVal A.n f.val i')
            else
              let j := i' - d
              let s_j := S.getD j f
              if a = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i')) = fkPart f.val A.k := by
        unfold fkPart
        refine List.flatMap_congr fun a ha_mem => ?_
        rw [List.mem_range] at ha_mem
        rw [dif_neg hnq]
        dsimp only
        rw [if_pos ha_mem]
      have h2 : (List.range 2).flatMap (fun b =>
          if hq : A.n + i < A.n then
            if ha : A.k + b < A.k then
              encUnary (A.δ ⟨A.n + i, hq⟩ ⟨A.k + b, ha⟩).val
            else if A.n + i = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨A.n + i, hq⟩ ⟨0, by omega⟩).val
          else
            let i' := A.n + i - A.n
            if A.k + b < A.k then
              encUnary f.val
            else if i' < d then
              encUnary (phaseC1ExtraVal A.n f.val i')
            else
              let j := i' - d
              let s_j := S.getD j f
              if A.k + b = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i')) =
          encUnary (phaseC1ExtraVal A.n f.val i) ++ encUnary (phaseC1ExtraVal A.n f.val i) := by
        have hr2 : List.range 2 = [0, 1] := rfl
        have hna0 : ¬ (A.k + 0 < A.k) := by omega
        have hna1 : ¬ (A.k + 1 < A.k) := by omega
        rw [hr2]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
          dif_neg hnq, hsub, if_neg hna0, if_neg hna1, if_pos hi_mem]
      rw [hfk, h2]
      simp [phaseC1Row, List.append_assoc]
    have h_partC2 : (List.range S.length).flatMap (fun j =>
        (List.range (A.k + 2)).flatMap fun a =>
          if hq : A.n + (d + j) < A.n then
            if ha : a < A.k then
              encUnary (A.δ ⟨A.n + (d + j), hq⟩ ⟨a, ha⟩).val
            else if A.n + (d + j) = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨A.n + (d + j), hq⟩ ⟨0, by omega⟩).val
          else
            let i' := A.n + (d + j) - A.n
            if a < A.k then
              encUnary f.val
            else if i' < d then
              encUnary (phaseC1ExtraVal A.n f.val i')
            else
              let j' := i' - d
              let s_j := S.getD j' f
              if a = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i')) =
        phaseC2Table A.n A.k f.val (S.map Fin.val) d S.length := by
      unfold phaseC2Table
      refine List.flatMap_congr fun j hj_mem => ?_
      rw [List.mem_range] at hj_mem
      have hnq : ¬ (A.n + (d + j) < A.n) := by omega
      have hsub : A.n + (d + j) - A.n = d + j := by omega
      have hnd : ¬ (d + j < d) := by omega
      have hsub_d : d + j - d = j := by omega
      have hgetD : (S.map Fin.val).getD j 0 = (S.getD j f).val :=
        getD_map_val_sourcesOf A hn_pos j hj_mem
      rw [flatMap_range_add A.k 2]
      have hfk : (List.range A.k).flatMap (fun a =>
          if hq : A.n + (d + j) < A.n then
            if ha : a < A.k then
              encUnary (A.δ ⟨A.n + (d + j), hq⟩ ⟨a, ha⟩).val
            else if A.n + (d + j) = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨A.n + (d + j), hq⟩ ⟨0, by omega⟩).val
          else
            let i' := A.n + (d + j) - A.n
            if a < A.k then
              encUnary f.val
            else if i' < d then
              encUnary (phaseC1ExtraVal A.n f.val i')
            else
              let j' := i' - d
              let s_j := S.getD j' f
              if a = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i')) = fkPart f.val A.k := by
        unfold fkPart
        refine List.flatMap_congr fun a ha_mem => ?_
        rw [List.mem_range] at ha_mem
        rw [dif_neg hnq]
        dsimp only
        rw [if_pos ha_mem]
      have h2 : (List.range 2).flatMap (fun b =>
          if hq : A.n + (d + j) < A.n then
            if ha : A.k + b < A.k then
              encUnary (A.δ ⟨A.n + (d + j), hq⟩ ⟨A.k + b, ha⟩).val
            else if A.n + (d + j) = f.val then
              encUnary A.n
            else
              encUnary (A.δ ⟨A.n + (d + j), hq⟩ ⟨0, by omega⟩).val
          else
            let i' := A.n + (d + j) - A.n
            if A.k + b < A.k then
              encUnary f.val
            else if i' < d then
              encUnary (phaseC1ExtraVal A.n f.val i')
            else
              let j' := i' - d
              let s_j := S.getD j' f
              if A.k + b = A.k then
                encUnary s_j.val
              else
                encUnary (phaseC2ExtraVal A.n s_j.val i')) =
          encUnary ((S.map Fin.val).getD j 0) ++
            encUnary (phaseC2ExtraVal A.n ((S.map Fin.val).getD j 0) (d + j)) := by
        have hr2 : List.range 2 = [0, 1] := rfl
        have hna0 : ¬ (A.k + 0 < A.k) := by omega
        have hna1 : ¬ (A.k + 1 < A.k) := by omega
        have hk0 : A.k + 0 = A.k := by omega
        have hk1 : A.k + 1 ≠ A.k := by omega
        rw [hr2]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
          dif_neg hnq, hsub, if_neg hna0, if_neg hna1, if_neg hnd, hsub_d,
          if_pos hk0, if_neg hk1, hgetD]
      rw [hfk, h2]
      simp [phaseC2Row, List.append_assoc]
    rw [h_partA, h_partC1, h_partC2]
    simp [headerRev, encUnary, d, List.reverse_append, List.append_assoc]
  · rw [if_neg h]
    have htable :
        (List.range A.n).flatMap (fun q ↦
          (List.range (A.k + 2)).flatMap (fun _ ↦ encUnary q)) =
        (List.finRange A.n).flatMap (fun q ↦
          (List.finRange (A.k + 2)).flatMap (fun _ ↦ encUnary q.val)) := by
      rw [← flatMap_finRange_eq_flatMap_range A.n]
      refine List.flatMap_congr fun q _ ↦ ?_
      rw [← flatMap_finRange_eq_flatMap_range (A.k + 2)]
    simp only [falseOutRev, List.reverse_reverse]
    rw [htable]
    unfold huffmanOfStronglyAcyclic
    rw [dif_neg h]
    simp [Automaton.encode, encUnary, List.append_assoc]

end HuffmanTotalFormula

-- Source: Solutions/Sol_SyncPrefix_Huffman_huffmanEncodeMap_polyTime.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open SyncPrefix.Huffman CookPvsNP

namespace HuffmanTotalPolyTime

open HuffmanTotalFormula

abbrev Sym := Option Bool

inductive SKey where
  | ki
  | ko
  | outRev
  | N
  | K
  | K2
  | NK
  | Nrem
  | Krem
  | Q
  | W
  | V0
  | F
  | C1
  | C2
  | Found
  | D
  | Scnt
  | Srev
  | S
  | sc
  deriving DecidableEq

instance : Fintype SKey where
  elems := {.ki, .ko, .outRev, .N, .K, .K2, .NK, .Nrem, .Krem, .Q, .W, .V0,
            .F, .C1, .C2, .Found, .D, .Scnt, .Srev, .S, .sc}
  complete x := by cases x <;> decide

abbrev Prog := StackProg SKey Sym
abbrev Store := SKey → List Sym

lemma exec_congr {p : Prog} {s t t' : Store} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

lemma exec_congr_left {p : Prog} {s s' t : Store} {n : ℕ}
    (h : p.Exec s t n) (hs : s' = s) : p.Exec s' t n := hs ▸ h

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

lemma head?_replicate_isSome (n : ℕ) (a : Sym) (hn : 0 < n) :
    (List.replicate n a).head?.isSome = true := by
  cases n with
  | zero => omega
  | succ n => rfl

lemma head?_replicate_isNone_false (n : ℕ) (a : Sym) (hn : 0 < n) :
    (List.replicate n a).head?.isNone = false := by
  cases n with
  | zero => omega
  | succ n => rfl

lemma drop_eq_getElem_cons {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

/-! ### Unary Emission and Stream Primitives -/

def emitUnaryTo (src dst : SKey) : Prog :=
  .seq (copyProg src dst .sc) (pushProg dst none)

lemma exec_emitUnaryTo (src dst : SKey) (hsd : src ≠ dst) (hst : src ≠ .sc) (hdt : dst ≠ .sc)
    (s : Store) (v : ℕ) (hsrc : s src = List.replicate v (some true)) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 5,
      (emitUnaryTo src dst).Exec s
        (Function.update s dst ((encUnary v).reverse ++ s dst)) c := by
  have e1 := stack_copy src dst .sc hsd hst hdt s hsc
  set s1 := Function.update s dst (s src ++ s dst)
  have e2 := (stack_basic_macros dst s1).1 none
  refine ⟨(6 * (s src).length + 3) + 1 + 1, by simp [hsrc], ?_⟩
  refine exec_congr (StackProg.Exec.seq e1 e2) ?_
  funext k
  cases k <;> simp [s1, hsrc, encUnary, List.reverse_append]

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

lemma length_nextWord_le (w : List Sym) : (nextWord w).length ≤ w.length := by
  simp [nextWord]

lemma length_wordAt_le (w : List Sym) : ∀ i : ℕ, (wordAt w i).length ≤ w.length
  | 0 => le_rfl
  | i + 1 => le_trans (length_nextWord_le (wordAt w i)) (length_wordAt_le w i)

lemma valAt_le_length (w : List Sym) (i : ℕ) : valAt w i ≤ w.length :=
  le_trans (leadOnes_le (wordAt w i)) (length_wordAt_le w i)

def readUnaryAct (src dst : SKey) (_h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = src then .pop else if k = dst then .push (some true) else .keep

def readUnaryLoop (src dst : SKey) : Prog :=
  .loop (fun h => decide (h src = some (some true))) (.act (readUnaryAct src dst))

def readUnaryProg (src dst : SKey) : Prog :=
  .seq (readUnaryLoop src dst) (popProg src)

def sReadUnary (src dst : SKey) (s : Store) (i : ℕ) : Store :=
  Function.update (Function.update s src ((s src).drop i))
    dst (List.replicate i (some true))

lemma exec_readUnaryProg_raw (src dst : SKey) (hsd : src ≠ dst)
    (s : Store) (hdst : s dst = []) :
    ∃ c ≤ 3 * leadOnes (s src) + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src (nextWord (s src)))
          dst (List.replicate (leadOnes (s src)) (some true))) c := by
  have hloop : ∃ c1 ≤ leadOnes (s src) * 3 + 1,
      (readUnaryLoop src dst).Exec (sReadUnary src dst s 0)
        (sReadUnary src dst s (leadOnes (s src))) c1 := by
    refine exec_bounded_loop (fun h => decide (h src = some (some true)))
      (.act (readUnaryAct src dst)) (leadOnes (s src)) (sReadUnary src dst s) 1 ?_ ?_ ?_
    · intro i hi
      have hsrc_i : sReadUnary src dst s i src = (s src).drop i := by
        simp [sReadUnary, hsd]
      dsimp only
      rw [decide_eq_true_eq, hsrc_i]
      exact head?_drop_of_lt_leadOnes (s src) i hi
    · have hsrc_n : sReadUnary src dst s (leadOnes (s src)) src = (s src).drop (leadOnes (s src)) := by
        simp [sReadUnary, hsd]
      dsimp only
      rw [decide_eq_false_iff_not, hsrc_n]
      exact head?_drop_leadOnes (s src)
    · intro i _
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act (readUnaryAct src dst) (sReadUnary src dst s i)) ?_⟩
      funext k
      by_cases hks : k = src
      · subst hks
        simp [StackProg.applyAct, readUnaryAct, sReadUnary, hsd, StackAct.apply, tail_drop_eq_drop_succ]
      · by_cases hkd : k = dst
        · subst hkd
          simp [StackProg.applyAct, readUnaryAct, sReadUnary, hks, StackAct.apply, List.replicate_succ]
        · simp [StackProg.applyAct, readUnaryAct, sReadUnary, hks, hkd, StackAct.apply]
  have h0 : s = sReadUnary src dst s 0 := by
    funext k
    by_cases hks : k = src
    · subst hks; simp [sReadUnary, hsd]
    · by_cases hkd : k = dst
      · subst hkd; simp [sReadUnary, hdst]
      · simp [sReadUnary, hks, hkd]
  rcases hloop with ⟨c1, hc1, eloop⟩
  have hloop' : ∃ c1 ≤ leadOnes (s src) * 3 + 1,
      (readUnaryLoop src dst).Exec s
        (sReadUnary src dst s (leadOnes (s src))) c1 := ⟨c1, hc1, exec_congr_left eloop h0⟩
  have hpop : ∃ c2 ≤ 1, (popProg src).Exec (sReadUnary src dst s (leadOnes (s src)))
      (Function.update (Function.update s src (nextWord (s src)))
        dst (List.replicate (leadOnes (s src)) (some true))) c2 := by
    refine ⟨1, le_rfl, exec_congr (stack_basic_macros src (sReadUnary src dst s (leadOnes (s src)))).2.1 ?_⟩
    funext k
    by_cases hks : k = src
    · subst hks; simp [sReadUnary, hsd, nextWord]
    · by_cases hkd : k = dst
      · subst hkd; simp [sReadUnary, hks]
      · simp [sReadUnary, hks, hkd]
  exact exec_le_of_le (exec_seq_le hloop' hpop) (by omega)

lemma exec_readUnaryProg_wordAt (src dst : SKey) (hsd : src ≠ dst)
    (s : Store) (w : List Sym) (idx : ℕ)
    (hsrc : s src = wordAt w idx) (hdst : s dst = []) :
    ∃ c ≤ 3 * w.length + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src (wordAt w (idx + 1)))
          dst (List.replicate (valAt w idx) (some true))) c := by
  have hraw := exec_readUnaryProg_raw src dst hsd s hdst
  rw [hsrc] at hraw
  have hv : leadOnes (wordAt w idx) ≤ w.length := valAt_le_length w idx
  exact exec_le_of_le hraw (by omega)

/-! ### Equality Comparison Subroutine (`branchEqVQ`) -/

def prepCompareProg : Prog :=
  .seq (copyProg .V0 .C1 .sc)
    (.seq (copyProg .Q .C2 .sc)
      (syncPopProg .C1 .C2))

def cleanCompareProg : Prog :=
  .seq (clearProg .C1) (clearProg .C2)

def isEqTest (h : SKey → Option Sym) : Bool :=
  (h .C1).isNone && (h .C2).isNone

def branchEqVQ (trueProg falseProg : Prog) : Prog :=
  .seq prepCompareProg
    (.branch isEqTest
      (.seq cleanCompareProg trueProg)
      (.seq cleanCompareProg falseProg))

def cmpStore (s : Store) (v q : ℕ) : Store :=
  Function.update (Function.update s .C1 (List.replicate (v - min v q) (some true)))
    .C2 (List.replicate (q - min v q) (some true))

lemma isEqTest_cmpStore (s : Store) (v q : ℕ) :
    isEqTest (fun k => (cmpStore s v q k).head?) = decide (v = q) := by
  unfold isEqTest cmpStore
  simp only [Function.update_self, Function.update_of_ne (by decide : SKey.C1 ≠ SKey.C2)]
  by_cases hvq : v = q
  · subst hvq
    simp
  · by_cases hlt : v < q
    · have hmin : min v q = v := Nat.min_eq_left (le_of_lt hlt)
      have hpos : 0 < q - v := by omega
      have hne := head?_replicate_isNone_false (q - v) (some true) hpos
      simp [hmin, hne, hvq]
    · have hgt : q < v := by omega
      have hmin : min v q = q := Nat.min_eq_right (le_of_lt hgt)
      have hpos : 0 < v - q := by omega
      have hne := head?_replicate_isNone_false (v - q) (some true) hpos
      simp [hmin, hne, hvq]

lemma exec_prepCompareProg (s : Store) (v q : ℕ)
    (hV0 : s .V0 = List.replicate v (some true))
    (hQ : s .Q = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 9 * q + 9,
      prepCompareProg.Exec s (cmpStore s v q) c := by
  have hc1 := stack_copy SKey.V0 SKey.C1 SKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .C1 (s .V0 ++ s .C1)
  have e1 : ∃ c ≤ 6 * v + 3, (copyProg .V0 .C1 .sc).Exec s s1 c :=
    ⟨6 * (s .V0).length + 3, by simp [hV0], hc1⟩
  have hc2 := stack_copy SKey.Q SKey.C2 SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, hsc])
  set s2 := Function.update s1 .C2 (s1 .Q ++ s1 .C2)
  have e2 : ∃ c ≤ 6 * q + 3, (copyProg .Q .C2 .sc).Exec s1 s2 c :=
    ⟨6 * (s1 .Q).length + 3, by simp [s1, hQ], hc2⟩
  have hsync := stack_sync_pop SKey.C1 SKey.C2 (by decide) s2
  have hs2_C1 : (s2 .C1).length = v := by simp [s2, s1, hV0, hC1]
  have hs2_C2 : (s2 .C2).length = q := by simp [s2, s1, hQ, hC2]
  have e3 : ∃ c ≤ 3 * q + 1, (syncPopProg .C1 .C2).Exec s2 (cmpStore s v q) c := by
    refine ⟨3 * min (s2 .C1).length (s2 .C2).length + 1, ?_, exec_congr hsync ?_⟩
    · rw [hs2_C1, hs2_C2]
      have : min v q ≤ q := Nat.min_le_right v q
      omega
    · funext k
      cases k <;> simp [s2, s1, cmpStore, hV0, hQ, hC1, hC2, List.drop_replicate]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

lemma exec_cleanCompareProg (s : Store) (v q : ℕ)
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) :
    ∃ c ≤ 3 * v + 3 * q + 3,
      cleanCompareProg.Exec (cmpStore s v q) s c := by
  have hc1 := (stack_basic_macros SKey.C1 (cmpStore s v q)).2.2
  set s1 := Function.update (cmpStore s v q) .C1 []
  have e1 : ∃ c ≤ 3 * v + 1, (clearProg .C1).Exec (cmpStore s v q) s1 c := by
    refine ⟨3 * (cmpStore s v q .C1).length + 1, ?_, hc1⟩
    simp [cmpStore]
  have hc2 := (stack_basic_macros SKey.C2 s1).2.2
  have e2 : ∃ c ≤ 3 * q + 1, (clearProg .C2).Exec s1 s c := by
    refine ⟨3 * (s1 .C2).length + 1, ?_, exec_congr hc2 ?_⟩
    · simp [s1, cmpStore]
    · funext k
      cases k <;> simp [s1, cmpStore, hC1, hC2]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

lemma exec_branchEqVQ_true (trueProg falseProg : Prog) (s t : Store) (v q B : ℕ)
    (hV0 : s .V0 = List.replicate v (some true))
    (hQ : s .Q = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = [])
    (heq : v = q) (ht : ∃ c ≤ B, trueProg.Exec s t c) :
    ∃ c ≤ 9 * v + 12 * q + 15 + B,
      (branchEqVQ trueProg falseProg).Exec s t c := by
  have e1 := exec_prepCompareProg s v q hV0 hQ hC1 hC2 hsc
  have htest : isEqTest (fun k => (cmpStore s v q k).head?) = true := by
    rw [isEqTest_cmpStore, decide_eq_true_eq]
    exact heq
  have e_clean := exec_cleanCompareProg s v q hC1 hC2
  have e_br := exec_branch_true_le isEqTest
    (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg)
    htest (exec_seq_le e_clean ht)
  exact exec_le_of_le (exec_seq_le e1 e_br) (by omega)

lemma exec_branchEqVQ_false (trueProg falseProg : Prog) (s t : Store) (v q B : ℕ)
    (hV0 : s .V0 = List.replicate v (some true))
    (hQ : s .Q = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = [])
    (hne : v ≠ q) (hf : ∃ c ≤ B, falseProg.Exec s t c) :
    ∃ c ≤ 9 * v + 12 * q + 15 + B,
      (branchEqVQ trueProg falseProg).Exec s t c := by
  have e1 := exec_prepCompareProg s v q hV0 hQ hC1 hC2 hsc
  have htest : isEqTest (fun k => (cmpStore s v q k).head?) = false := by
    rw [isEqTest_cmpStore, decide_eq_false_iff_not]
    exact hne
  have e_clean := exec_cleanCompareProg s v q hC1 hC2
  have e_br := exec_branch_false_le isEqTest
    (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg)
    htest (exec_seq_le e_clean hf)
  exact exec_le_of_le (exec_seq_le e1 e_br) (by omega)

def prepCompareQFProg : Prog :=
  .seq (copyProg .Q .C1 .sc)
    (.seq (copyProg .F .C2 .sc)
      (syncPopProg .C1 .C2))

def branchEqQF (trueProg falseProg : Prog) : Prog :=
  .seq prepCompareQFProg
    (.branch isEqTest
      (.seq cleanCompareProg trueProg)
      (.seq cleanCompareProg falseProg))

lemma exec_prepCompareQFProg (s : Store) (v q : ℕ)
    (hV0 : s .Q = List.replicate v (some true))
    (hQ : s .F = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 9 * q + 9,
      prepCompareQFProg.Exec s (cmpStore s v q) c := by
  have hc1 := stack_copy SKey.Q SKey.C1 SKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .C1 (s .Q ++ s .C1)
  have e1 : ∃ c ≤ 6 * v + 3, (copyProg .Q .C1 .sc).Exec s s1 c :=
    ⟨6 * (s .Q).length + 3, by simp [hV0], hc1⟩
  have hc2 := stack_copy SKey.F SKey.C2 SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, hsc])
  set s2 := Function.update s1 .C2 (s1 .F ++ s1 .C2)
  have e2 : ∃ c ≤ 6 * q + 3, (copyProg .F .C2 .sc).Exec s1 s2 c :=
    ⟨6 * (s1 .F).length + 3, by simp [s1, hQ], hc2⟩
  have hsync := stack_sync_pop SKey.C1 SKey.C2 (by decide) s2
  have hs2_C1 : (s2 .C1).length = v := by simp [s2, s1, hV0, hC1]
  have hs2_C2 : (s2 .C2).length = q := by simp [s2, s1, hQ, hC2]
  have e3 : ∃ c ≤ 3 * q + 1, (syncPopProg .C1 .C2).Exec s2 (cmpStore s v q) c := by
    refine ⟨3 * min (s2 .C1).length (s2 .C2).length + 1, ?_, exec_congr hsync ?_⟩
    · rw [hs2_C1, hs2_C2]
      have : min v q ≤ q := Nat.min_le_right v q
      omega
    · funext k
      cases k <;> simp [s2, s1, cmpStore, hV0, hQ, hC1, hC2, List.drop_replicate]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

lemma exec_branchEqQF_true (trueProg falseProg : Prog) (s t : Store) (v q B : ℕ)
    (hV0 : s .Q = List.replicate v (some true))
    (hQ : s .F = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = [])
    (heq : v = q) (ht : ∃ c ≤ B, trueProg.Exec s t c) :
    ∃ c ≤ 9 * v + 12 * q + 15 + B,
      (branchEqQF trueProg falseProg).Exec s t c := by
  have e1 := exec_prepCompareQFProg s v q hV0 hQ hC1 hC2 hsc
  have htest : isEqTest (fun k => (cmpStore s v q k).head?) = true := by
    rw [isEqTest_cmpStore, decide_eq_true_eq]
    exact heq
  have e_clean := exec_cleanCompareProg s v q hC1 hC2
  have e_br := exec_branch_true_le isEqTest
    (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg)
    htest (exec_seq_le e_clean ht)
  exact exec_le_of_le (exec_seq_le e1 e_br) (by omega)

lemma exec_branchEqQF_false (trueProg falseProg : Prog) (s t : Store) (v q B : ℕ)
    (hV0 : s .Q = List.replicate v (some true))
    (hQ : s .F = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = [])
    (hne : v ≠ q) (hf : ∃ c ≤ B, falseProg.Exec s t c) :
    ∃ c ≤ 9 * v + 12 * q + 15 + B,
      (branchEqQF trueProg falseProg).Exec s t c := by
  have e1 := exec_prepCompareQFProg s v q hV0 hQ hC1 hC2 hsc
  have htest : isEqTest (fun k => (cmpStore s v q k).head?) = false := by
    rw [isEqTest_cmpStore, decide_eq_false_iff_not]
    exact hne
  have e_clean := exec_cleanCompareProg s v q hC1 hC2
  have e_br := exec_branch_false_le isEqTest
    (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg)
    htest (exec_seq_le e_clean hf)
  exact exec_le_of_le (exec_seq_le e1 e_br) (by omega)

/-! ### Stage 1: Read `N`, `K`, initialize `K2` and `Nrem` -/

def initHeaderReadProg : Prog :=
  .seq (readUnaryProg .ki .N)
    (.seq (readUnaryProg .ki .K)
      (.seq (copyProg .K .K2 .sc)
        (.seq (pushProg .K2 (some true))
          (.seq (pushProg .K2 (some true))
            (.seq (copyProg .N .Nrem .sc)
              (popProg .Nrem))))))

def storeAfterHeaderRead (n k : ℕ) (body : List Sym) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .Nrem => List.replicate (n - 1) (some true)
  | _ => []

lemma exec_initHeaderReadProg (w : List Sym) :
    let n := valAt w 0
    let k := valAt w 1
    let body := wordAt w 2
    ∃ c ≤ 18 * w.length + 25,
      initHeaderReadProg.Exec (fun j => if j = .ki then w else [])
        (storeAfterHeaderRead n k body) c := by
  intro n k body
  set s0 : Store := fun j => if j = .ki then w else []
  have e1 := exec_readUnaryProg_wordAt .ki .N (by decide) s0 w 0 rfl rfl
  set s1 := Function.update (Function.update s0 .ki (wordAt w 1)) .N (List.replicate n (some true))
  have e2 := exec_readUnaryProg_wordAt .ki .K (by decide) s1 w 1
    (by simp [s1]) (by simp [s1, s0])
  set s2 := Function.update (Function.update s1 .ki body) .K (List.replicate k (some true))
  have hc3 := stack_copy SKey.K SKey.K2 SKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, s0])
  set s3 := Function.update s2 .K2 (s2 .K ++ s2 .K2)
  have e3 : ∃ c ≤ 6 * k + 3, (copyProg .K .K2 .sc).Exec s2 s3 c :=
    ⟨6 * (s2 .K).length + 3, by simp [s2], hc3⟩
  have hp4 := (stack_basic_macros SKey.K2 s3).1 (some true)
  set s4 := Function.update s3 .K2 (some true :: s3 .K2)
  have e4 : ∃ c ≤ 1, (pushProg .K2 (some true)).Exec s3 s4 c := ⟨1, le_rfl, hp4⟩
  have hp5 := (stack_basic_macros SKey.K2 s4).1 (some true)
  set s5 := Function.update s4 .K2 (some true :: s4 .K2)
  have e5 : ∃ c ≤ 1, (pushProg .K2 (some true)).Exec s4 s5 c := ⟨1, le_rfl, hp5⟩
  have hc6 := stack_copy SKey.N SKey.Nrem SKey.sc (by decide) (by decide) (by decide) s5
    (by simp [s5, s4, s3, s2, s1, s0])
  set s6 := Function.update s5 .Nrem (s5 .N ++ s5 .Nrem)
  have e6 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s5 s6 c :=
    ⟨6 * (s5 .N).length + 3, by simp [s5, s4, s3, s2, s1], hc6⟩
  have hp7 := (stack_basic_macros SKey.Nrem s6).2.1
  have e7 : ∃ c ≤ 1, (popProg .Nrem).Exec s6 (storeAfterHeaderRead n k body) c := by
    refine ⟨1, le_rfl, exec_congr hp7 ?_⟩
    funext j
    cases j <;> simp [s6, s5, s4, s3, s2, s1, s0, storeAfterHeaderRead, List.replicate_succ]
  have hn : n ≤ w.length := valAt_le_length w 0
  have hk : k ≤ w.length := valAt_le_length w 1
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 (exec_seq_le e5 (exec_seq_le e6 e7)))))
  exact exec_le_of_le e_all (by omega)

/-! ### Stage 2A: False Branch (`¬ (2 ≤ n ∧ 1 ≤ k)`) -/

def nkPorts : Fin 4 ↪ SKey where
  toFun
    | ⟨0, _⟩ => .K
    | ⟨1, _⟩ => .NK
    | ⟨2, _⟩ => .Nrem
    | ⟨_ + 3, _⟩ => .sc
  inj' := by decide

def trueInitProg : Prog :=
  .seq (clearProg .Nrem)
    (.seq (copyProg .N .Q .sc)
      (.seq (copyProg .N .Q .sc)
        (.seq (emitUnaryTo .Q .outRev)
          (.seq (clearProg .Q)
            (.seq (emitUnaryTo .K2 .outRev)
              (.seq (copyProg .N .Nrem .sc)
                (.seq (repeatCopyProg nkPorts)
                  (.seq (copyProg .ki .W .sc)
                    (copyProg .N .Nrem .sc)))))))))

lemma sinkValUpTo_le (k : ℕ) (body : List Sym) (q : ℕ) :
    sinkValUpTo k body q ≤ q := by
  unfold sinkValUpTo
  generalize he : (List.range q).filter (isSinkVal k body) = l
  cases l with
  | nil => simp
  | cons x xs =>
    have hx : x ∈ (List.range q).filter (isSinkVal k body) := by rw [he]; simp
    simp only [List.mem_filter, List.mem_range] at hx
    simpa using Nat.le_of_lt hx.1

def storeAfterSink (n k : ℕ) (body : List Sym) : Store :=
  Function.update (storeAfterHeaderRead n k body) .F
    (List.replicate (sinkValUpTo k body n) (some true))

def phaseAStore (n k : ℕ) (body : List Sym) (q₀ : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .NK => List.replicate (n * k) (some true)
  | .Nrem => List.replicate (n - q₀) (some true)
  | .Q => List.replicate q₀ (some true)
  | .W => wordAt body (q₀ * k)
  | .F => List.replicate (sinkValUpTo k body n) (some true)
  | .outRev => (phaseATable n k body q₀).reverse ++ headerRev n k
  | _ => []

lemma replicate_flatten_nk (n k : ℕ) :
    (List.replicate n (List.replicate k (some true))).flatten =
      List.replicate (n * k) (some true) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, ← List.replicate_add, Nat.succ_mul, add_comm]

lemma exec_trueInitProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 6 * n * k + 6 * body.length + 52 * n + 6 * k + 55,
      trueInitProg.Exec (storeAfterSink n k body) (phaseAStore n k body 0) c := by
  set s0 := storeAfterSink n k body
  have hc1 := (stack_basic_macros SKey.Nrem s0).2.2
  set s1 := Function.update s0 .Nrem []
  have e1 : ∃ c ≤ 3 * n + 1, (clearProg .Nrem).Exec s0 s1 c :=
    ⟨3 * (s0 .Nrem).length + 1, by simp [s0, storeAfterSink, storeAfterHeaderRead], hc1⟩
  have hc2 := stack_copy SKey.N SKey.Q SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s2 := Function.update s1 .Q (s1 .N ++ s1 .Q)
  have e2 : ∃ c ≤ 6 * n + 3, (copyProg .N .Q .sc).Exec s1 s2 c :=
    ⟨6 * (s1 .N).length + 3, by simp [s1, s0, storeAfterSink, storeAfterHeaderRead], hc2⟩
  have hc3 := stack_copy SKey.N SKey.Q SKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s3 := Function.update s2 .Q (s2 .N ++ s2 .Q)
  have e3 : ∃ c ≤ 6 * n + 3, (copyProg .N .Q .sc).Exec s2 s3 c :=
    ⟨6 * (s2 .N).length + 3, by simp [s2, s1, s0, storeAfterSink, storeAfterHeaderRead], hc3⟩
  have hs3_Q : s3 .Q = List.replicate (2 * n) (some true) := by
    simp [s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead, two_mul]
  have e4 := exec_emitUnaryTo .Q .outRev (by decide) (by decide) (by decide) s3 (2 * n)
    hs3_Q (by simp [s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s4 := Function.update s3 .outRev ((encUnary (2 * n)).reverse ++ s3 .outRev)
  have hc5 := (stack_basic_macros SKey.Q s4).2.2
  set s5 := Function.update s4 .Q []
  have e5 : ∃ c ≤ 6 * n + 1, (clearProg .Q).Exec s4 s5 c :=
    ⟨3 * (s4 .Q).length + 1, by simp [s4, hs3_Q]; omega, hc5⟩
  have e6 := exec_emitUnaryTo .K2 .outRev (by decide) (by decide) (by decide) s5 (k + 2)
    (by simp [s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
    (by simp [s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s6 := Function.update s5 .outRev ((encUnary (k + 2)).reverse ++ s5 .outRev)
  have hc7 := stack_copy SKey.N SKey.Nrem SKey.sc (by decide) (by decide) (by decide) s6
    (by simp [s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s7 := Function.update s6 .Nrem (s6 .N ++ s6 .Nrem)
  have e7 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s6 s7 c :=
    ⟨6 * (s6 .N).length + 3, by simp [s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead], hc7⟩
  have hrep := stack_repeat_copy nkPorts s7
    (by simp [nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s8 := Function.update (Function.update s7 (nkPorts 2) []) (nkPorts 1)
    ((List.replicate (s7 (nkPorts 2)).length (s7 (nkPorts 0))).flatten ++ s7 (nkPorts 1))
  have e8 : ∃ c ≤ 6 * n * k + 7 * n + 1, (repeatCopyProg nkPorts).Exec s7 s8 c := by
    refine ⟨(6 * (s7 (nkPorts 0)).length + 7) * (s7 (nkPorts 2)).length + 1, ?_, hrep⟩
    have hK_len : (s7 (nkPorts 0)).length = k := by
      simp [nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead]
    have hN_len : (s7 (nkPorts 2)).length = n := by
      simp [nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead]
    rw [hK_len, hN_len]
    ring_nf
    omega
  have hc9 := stack_copy SKey.ki SKey.W SKey.sc (by decide) (by decide) (by decide) s8
    (by simp [s8, nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  set s9 := Function.update s8 .W (s8 .ki ++ s8 .W)
  have e9 : ∃ c ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s8 s9 c :=
    ⟨6 * (s8 .ki).length + 3, by simp [s8, nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead], hc9⟩
  have hc10 := stack_copy SKey.N SKey.Nrem SKey.sc (by decide) (by decide) (by decide) s9
    (by simp [s9, s8, nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead])
  have e10 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s9 (phaseAStore n k body 0) c := by
    refine ⟨6 * (s9 .N).length + 3,
      by simp [s9, s8, nkPorts, s7, s6, s5, s4, s3, s2, s1, s0, storeAfterSink, storeAfterHeaderRead],
      exec_congr hc10 ?_⟩
    funext j
    cases j <;> simp [s9, s8, nkPorts, s7, s6, s5, s4, s3, s2, s1, s0,
      storeAfterSink, storeAfterHeaderRead, phaseAStore, phaseATable, headerRev, wordAt, sinkValUpTo,
      replicate_flatten_nk]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 (exec_seq_le e5
    (exec_seq_le e6 (exec_seq_le e7 (exec_seq_le e8 (exec_seq_le e9 e10))))))))
  exact exec_le_of_le e_all (by omega)

/-! ### Stage 2B.2: Phase A (`phaseALoopProg`) -/

def phaseAMidBodyProg : Prog :=
  .seq (popProg .Krem)
    (.seq (readUnaryProg .W .S)
      (.seq (emitUnaryTo .S .outRev)
        (clearProg .S)))

def phaseAMidLoopProg : Prog :=
  .loop (fun h => (h .Krem).isSome) phaseAMidBodyProg

def phaseATrueExtraProg : Prog :=
  .seq (emitUnaryTo .N .outRev) (emitUnaryTo .N .outRev)

def phaseAFalseExtraProg : Prog :=
  .seq (emitUnaryTo .V0 .outRev)
    (emitUnaryTo .V0 .outRev)

def phaseABodyProg : Prog :=
  .seq (popProg .Nrem)
    (.seq (readUnaryProg .W .V0)
      (.seq (emitUnaryTo .V0 .outRev)
        (.seq (copyProg .K .Krem .sc)
          (.seq (popProg .Krem)
            (.seq phaseAMidLoopProg
              (.seq (branchEqQF phaseATrueExtraProg phaseAFalseExtraProg)
                (.seq (clearProg .V0)
                  (pushProg .Q (some true)))))))))

def phaseALoopProg : Prog :=
  .loop (fun h => (h .Nrem).isSome) phaseABodyProg

def phaseAMidStore (n k : ℕ) (body : List Sym) (q₀ idx : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .NK => List.replicate (n * k) (some true)
  | .Nrem => List.replicate (n - (q₀ + 1)) (some true)
  | .Krem => List.replicate (k - 1 - idx) (some true)
  | .Q => List.replicate q₀ (some true)
  | .W => wordAt body (q₀ * k + 1 + idx)
  | .V0 => List.replicate (valAt body (q₀ * k)) (some true)
  | .F => List.replicate (sinkValUpTo k body n) (some true)
  | .outRev =>
      (phaseAMidPart k body q₀ idx).reverse ++
        (encUnary (valAt body (q₀ * k))).reverse ++
        (phaseATable n k body q₀).reverse ++ headerRev n k
  | _ => []

lemma phaseAMidPart_zero (k : ℕ) (body : List Sym) (q₀ : ℕ) :
    phaseAMidPart k body q₀ 0 = [] := rfl

lemma phaseAMidPart_succ (k : ℕ) (body : List Sym) (q₀ idx : ℕ) :
    phaseAMidPart k body q₀ (idx + 1) =
      phaseAMidPart k body q₀ idx ++ encUnary (valAt body (q₀ * k + 1 + idx)) := by
  simp [phaseAMidPart, List.range_succ]

lemma phaseATable_succ (n k : ℕ) (body : List Sym) (q₀ : ℕ) :
    phaseATable n k body (q₀ + 1) = phaseATable n k body q₀ ++ phaseARow n k body q₀ := by
  simp [phaseATable, List.range_succ]

lemma exec_phaseAMidLoopProg (n k : ℕ) (body : List Sym) (q₀ : ℕ) :
    ∃ c ≤ (k - 1) * (12 * body.length + 15) + 1,
      phaseAMidLoopProg.Exec (phaseAMidStore n k body q₀ 0)
        (phaseAMidStore n k body q₀ (k - 1)) c := by
  refine exec_bounded_loop (fun h => (h .Krem).isSome) phaseAMidBodyProg (k - 1)
    (phaseAMidStore n k body q₀) (12 * body.length + 13) ?_ ?_ ?_
  · intro idx hidx
    simp [phaseAMidStore, head?_replicate_isSome, Nat.sub_pos_of_lt hidx]
  · simp [phaseAMidStore]
  · intro idx _
    set s0 := phaseAMidStore n k body q₀ idx
    have hp1 := (stack_basic_macros SKey.Krem s0).2.1
    set s1 := Function.update s0 .Krem (s0 .Krem).tail
    have e1 : ∃ c ≤ 1, (popProg .Krem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
    have e2 := exec_readUnaryProg_wordAt .W .S (by decide) s1 body (q₀ * k + 1 + idx)
      (by simp [s1, s0, phaseAMidStore]) (by simp [s1, s0, phaseAMidStore])
    set s2 := Function.update (Function.update s1 .W (wordAt body (q₀ * k + 1 + idx + 1)))
      .S (List.replicate (valAt body (q₀ * k + 1 + idx)) (some true))
    have e3 := exec_emitUnaryTo .S .outRev (by decide) (by decide) (by decide) s2
      (valAt body (q₀ * k + 1 + idx))
      (by simp [s2]) (by simp [s2, s1, s0, phaseAMidStore])
    set s3 := Function.update s2 .outRev ((encUnary (valAt body (q₀ * k + 1 + idx))).reverse ++ s2 .outRev)
    have hc4 := (stack_basic_macros SKey.S s3).2.2
    have hv_le : valAt body (q₀ * k + 1 + idx) ≤ body.length := valAt_le_length body _
    have e4 : ∃ c ≤ 3 * body.length + 1,
        (clearProg .S).Exec s3 (phaseAMidStore n k body q₀ (idx + 1)) c := by
      refine ⟨3 * (s3 .S).length + 1, ?_, exec_congr hc4 ?_⟩
      · simp [s3, s2]
        omega
      · funext j
        cases j <;> simp [s3, s2, s1, s0, phaseAMidStore, phaseAMidPart_succ,
          Nat.sub_sub, List.reverse_append, add_assoc]
    have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))
    exact exec_le_of_le e_all (by omega)

lemma exec_phaseABodyProg (n k : ℕ) (hk : 1 ≤ k) (body : List Sym) (q₀ : ℕ) (hq₀ : q₀ < n) :
    ∃ c ≤ (k - 1) * (12 * body.length + 15) + 33 * body.length + 40 * n + 6 * k + 65,
      phaseABodyProg.Exec (phaseAStore n k body q₀) (phaseAStore n k body (q₀ + 1)) c := by
  set s0 := phaseAStore n k body q₀
  have hp1 := (stack_basic_macros SKey.Nrem s0).2.1
  set s1 := Function.update s0 .Nrem (s0 .Nrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Nrem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have e2 := exec_readUnaryProg_wordAt .W .V0 (by decide) s1 body (q₀ * k)
    (by simp [s1, s0, phaseAStore]) (by simp [s1, s0, phaseAStore])
  set s2 := Function.update (Function.update s1 .W (wordAt body (q₀ * k + 1)))
    .V0 (List.replicate (valAt body (q₀ * k)) (some true))
  have e3 := exec_emitUnaryTo .V0 .outRev (by decide) (by decide) (by decide) s2
    (valAt body (q₀ * k)) (by simp [s2]) (by simp [s2, s1, s0, phaseAStore])
  set s3 := Function.update s2 .outRev ((encUnary (valAt body (q₀ * k))).reverse ++ s2 .outRev)
  have hc4 := stack_copy SKey.K SKey.Krem SKey.sc (by decide) (by decide) (by decide) s3
    (by simp [s3, s2, s1, s0, phaseAStore])
  set s4 := Function.update s3 .Krem (s3 .K ++ s3 .Krem)
  have e4 : ∃ c ≤ 6 * k + 3, (copyProg .K .Krem .sc).Exec s3 s4 c :=
    ⟨6 * (s3 .K).length + 3, by simp [s3, s2, s1, s0, phaseAStore], hc4⟩
  have hp5 := (stack_basic_macros SKey.Krem s4).2.1
  have e5 : ∃ c ≤ 1, (popProg .Krem).Exec s4 (phaseAMidStore n k body q₀ 0) c := by
    refine ⟨1, le_rfl, exec_congr hp5 ?_⟩
    funext j
    cases j <;> simp [s4, s3, s2, s1, s0, phaseAStore, phaseAMidStore, phaseAMidPart_zero, Nat.sub_sub]
  have e6 := exec_phaseAMidLoopProg n k body q₀
  set s6 := phaseAMidStore n k body q₀ (k - 1)
  set s7_target : Store := Function.update s6 .outRev ((encUnary (extraVal n k body q₀)).reverse ++ (encUnary (extraVal n k body q₀)).reverse ++ s6 .outRev)
  have hv0_le : valAt body (q₀ * k) ≤ body.length := valAt_le_length body (q₀ * k)
  have hf_le : sinkValUpTo k body n ≤ n := sinkValUpTo_le k body n
  have e7 : ∃ c ≤ 21 * body.length + 40 * n + 40,
      (branchEqQF phaseATrueExtraProg phaseAFalseExtraProg).Exec s6 s7_target c := by
    by_cases hvq : q₀ = sinkValUpTo k body n
    · have et1 := exec_emitUnaryTo .N .outRev (by decide) (by decide) (by decide) s6 n
        (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore])
      set st1 := Function.update s6 .outRev ((encUnary n).reverse ++ s6 .outRev)
      have et2 := exec_emitUnaryTo .N .outRev (by decide) (by decide) (by decide) st1 n
        (by simp [st1, s6, phaseAMidStore]) (by simp [st1, s6, phaseAMidStore])
      have et2' : ∃ c ≤ 6 * n + 5, (emitUnaryTo .N .outRev).Exec st1 s7_target c := by
        rcases et2 with ⟨c, hc, he⟩
        refine ⟨c, hc, exec_congr he ?_⟩
        funext j
        cases j <;> simp [st1, s7_target, extraVal, hvq]
      have ebr := exec_branchEqQF_true phaseATrueExtraProg phaseAFalseExtraProg s6 s7_target
        q₀ (sinkValUpTo k body n) (6 * n + 5 + 1 + (6 * n + 5))
        (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore])
        (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore])
        hvq (exec_seq_le et1 et2')
      exact exec_le_of_le ebr (by omega)
    · have ef1 := exec_emitUnaryTo .V0 .outRev (by decide) (by decide) (by decide) s6
        (valAt body (q₀ * k)) (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore])
      set sf1 := Function.update s6 .outRev ((encUnary (valAt body (q₀ * k))).reverse ++ s6 .outRev)
      have ef2 := exec_emitUnaryTo .V0 .outRev (by decide) (by decide) (by decide) sf1
        (valAt body (q₀ * k)) (by simp [sf1, s6, phaseAMidStore]) (by simp [sf1, s6, phaseAMidStore])
      have ef2' : ∃ c ≤ 6 * valAt body (q₀ * k) + 5, (emitUnaryTo .V0 .outRev).Exec sf1 s7_target c := by
        rcases ef2 with ⟨c, hc, he⟩
        refine ⟨c, hc, exec_congr he ?_⟩
        funext j
        cases j <;> simp [sf1, s7_target, extraVal, hvq]
      have ebr := exec_branchEqQF_false phaseATrueExtraProg phaseAFalseExtraProg s6 s7_target
        q₀ (sinkValUpTo k body n)
        (6 * valAt body (q₀ * k) + 5 + 1 + (6 * valAt body (q₀ * k) + 5))
        (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore])
        (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore]) (by simp [s6, phaseAMidStore])
        hvq (exec_seq_le ef1 ef2')
      exact exec_le_of_le ebr (by omega)
  have hc8 := (stack_basic_macros SKey.V0 s7_target).2.2
  set s8 := Function.update s7_target .V0 []
  have e8 : ∃ c ≤ 3 * body.length + 1, (clearProg .V0).Exec s7_target s8 c := by
    refine ⟨3 * (s7_target .V0).length + 1, ?_, hc8⟩
    simp [s7_target, s6, phaseAMidStore]
    omega
  have hp9 := (stack_basic_macros SKey.Q s8).1 (some true)
  have h_idx_eq : q₀ * k + 1 + (k - 1) = (q₀ + 1) * k := by
    rw [Nat.succ_mul]
    omega
  have e9 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec s8 (phaseAStore n k body (q₀ + 1)) c := by
    refine ⟨1, le_rfl, exec_congr hp9 ?_⟩
    funext j
    cases j <;> simp [s8, s7_target, s6, phaseAMidStore, phaseAStore, phaseATable_succ,
      phaseARow, List.replicate_succ, List.reverse_append, h_idx_eq]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4
    (exec_seq_le e5 (exec_seq_le e6 (exec_seq_le e7 (exec_seq_le e8 e9)))))))
  exact exec_le_of_le e_all (by omega)



lemma exec_phaseALoopProg (n k : ℕ) (hk : 1 ≤ k) (body : List Sym) :
    let B := (k - 1) * (12 * body.length + 15) + 33 * body.length + 40 * n + 6 * k + 65
    ∃ c ≤ n * (B + 2) + 1,
      phaseALoopProg.Exec (phaseAStore n k body 0) (phaseAStore n k body n) c := by
  intro _B
  refine exec_bounded_loop (fun h => (h .Nrem).isSome) phaseABodyProg n
    (phaseAStore n k body) _ ?_ ?_ ?_
  · intro q₀ hq₀
    simp [phaseAStore, head?_replicate_isSome, Nat.sub_pos_of_lt hq₀]
  · simp [phaseAStore]
  · intro q₀ hq₀
    exact exec_phaseABodyProg n k hk body q₀ hq₀

/-! ### Stage 2B.3: Phase B (`phaseAToBProg`, `phaseBLoopProg`, `phaseBToCProg`) -/

lemma sourceValsUpTo_succ_of_false (n k : ℕ) (body : List Sym) (q : ℕ)
    (h : isSourceVal n k body q = false) :
    sourceValsUpTo n k body (q + 1) = sourceValsUpTo n k body q := by
  simp [sourceValsUpTo, List.range_succ, List.filter_append, h]

lemma sourceValsUpTo_succ_of_true (n k : ℕ) (body : List Sym) (q : ℕ)
    (h : isSourceVal n k body q = true) :
    sourceValsUpTo n k body (q + 1) = sourceValsUpTo n k body q ++ [q] := by
  simp [sourceValsUpTo, List.range_succ, List.filter_append, h]

lemma isSourceUpTo_zero (n k : ℕ) (body : List Sym) (q : ℕ) :
    isSourceUpTo body (sinkValUpTo k body n) q 0 = decide (q ≠ sinkValUpTo k body n) := by simp [isSourceUpTo]

lemma isSourceUpTo_succ (n k : ℕ) (body : List Sym) (q idx : ℕ) :
    isSourceUpTo body (sinkValUpTo k body n) q (idx + 1) =
      (isSourceUpTo body (sinkValUpTo k body n) q idx && decide (valAt body idx ≠ q)) := by
  simp [isSourceUpTo, List.range_succ, Bool.and_assoc]

lemma length_sourceValsUpTo_le (n k : ℕ) (body : List Sym) (q : ℕ) :
    (sourceValsUpTo n k body q).length ≤ q := by
  simpa [sourceValsUpTo] using List.length_filter_le (isSourceVal n k body) (List.range q)

lemma getD_le_of_forall_le : ∀ (l : List ℕ) (B j : ℕ), (∀ x ∈ l, x ≤ B) → l.getD j 0 ≤ B
  | [], _, _, _ => Nat.zero_le _
  | x :: _, _B, 0, h => h x List.mem_cons_self
  | _ :: xs, B, j + 1, h => getD_le_of_forall_le xs B j (fun y hy => h y (List.mem_cons_of_mem _ hy))

lemma getD_sourceValsUpTo_le (n k : ℕ) (body : List Sym) (q j : ℕ) :
    (sourceValsUpTo n k body q).getD j 0 ≤ q := by
  refine getD_le_of_forall_le _ q j (fun x hx => ?_)
  simp only [sourceValsUpTo, List.mem_filter, List.mem_range] at hx
  exact le_of_lt hx.1

def phaseBStore (n k : ℕ) (body : List Sym) (q : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .NK => List.replicate (n * k) (some true)
  | .Nrem => List.replicate (n - q) (some true)
  | .Q => List.replicate q (some true)
  | .F => List.replicate (sinkValUpTo k body n) (some true)
  | .D => List.replicate (q - (sourceValsUpTo n k body q).length) (some true)
  | .Scnt => List.replicate (sourceValsUpTo n k body q).length (some true)
  | .Srev => ((sourceValsUpTo n k body q).flatMap encUnary).reverse
  | .outRev => (phaseATable n k body n).reverse ++ headerRev n k
  | _ => []

def phaseAToBProg : Prog :=
  .seq (clearProg .W)
    (.seq (clearProg .Q)
      (copyProg .N .Nrem .sc))

lemma exec_phaseAToBProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 3 * body.length + 9 * n + 7,
      phaseAToBProg.Exec (phaseAStore n k body n) (phaseBStore n k body 0) c := by
  set s0 := phaseAStore n k body n
  have hc1 := (stack_basic_macros SKey.W s0).2.2
  set s1 := Function.update s0 .W []
  have hw_le : (wordAt body (n * k)).length ≤ body.length := length_wordAt_le body (n * k)
  have e1 : ∃ c ≤ 3 * body.length + 1, (clearProg .W).Exec s0 s1 c := by
    refine ⟨3 * (s0 .W).length + 1, ?_, hc1⟩
    simp [s0, phaseAStore]
    omega
  have hc2 := (stack_basic_macros SKey.Q s1).2.2
  set s2 := Function.update s1 .Q []
  have e2 : ∃ c ≤ 3 * n + 1, (clearProg .Q).Exec s1 s2 c := by
    refine ⟨3 * (s1 .Q).length + 1, ?_, hc2⟩
    simp [s1, s0, phaseAStore]
  have hc3 := stack_copy SKey.N SKey.Nrem SKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, s0, phaseAStore])
  have e3 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s2 (phaseBStore n k body 0) c := by
    refine ⟨6 * (s2 .N).length + 3, by simp [s2, s1, s0, phaseAStore], exec_congr hc3 ?_⟩
    funext j
    cases j <;> simp [s2, s1, s0, phaseAStore, phaseBStore, sourceValsUpTo]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

def phaseBInnerBodyProg : Prog :=
  .seq (popProg .Krem)
    (.seq (readUnaryProg .W .V0)
      (.seq (branchEqVQ
          (.seq (clearProg .Found) (pushProg .Found (some true)))
          (popProg .sc))
        (clearProg .V0)))

def phaseBInnerLoopProg : Prog :=
  .loop (fun h => (h .Krem).isSome) phaseBInnerBodyProg

def phaseBBodyProg : Prog :=
  .seq (popProg .Nrem)
    (.seq (copyProg .ki .W .sc)
      (.seq (copyProg .NK .Krem .sc)
        (.seq (.seq (branchEqQF (pushProg .Found (some true)) (popProg .sc)) phaseBInnerLoopProg)
          (.seq (clearProg .W)
            (.seq (.branch (fun h => (h .Found).isNone)
                (.seq (emitUnaryTo .Q .Srev) (pushProg .Scnt (some true)))
                (.seq (clearProg .Found) (pushProg .D (some true))))
              (pushProg .Q (some true)))))))

def phaseBLoopProg : Prog :=
  .loop (fun h => (h .Nrem).isSome) phaseBBodyProg

def phaseBInnerStore (n k : ℕ) (body : List Sym) (q idx : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .NK => List.replicate (n * k) (some true)
  | .Nrem => List.replicate (n - (q + 1)) (some true)
  | .Krem => List.replicate (n * k - idx) (some true)
  | .Q => List.replicate q (some true)
  | .W => wordAt body idx
  | .F => List.replicate (sinkValUpTo k body n) (some true)
  | .Found => if isSourceUpTo body (sinkValUpTo k body n) q idx then [] else [some true]
  | .D => List.replicate (q - (sourceValsUpTo n k body q).length) (some true)
  | .Scnt => List.replicate (sourceValsUpTo n k body q).length (some true)
  | .Srev => ((sourceValsUpTo n k body q).flatMap encUnary).reverse
  | .outRev => (phaseATable n k body n).reverse ++ headerRev n k
  | _ => []

lemma exec_phaseBInnerLoopProg (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ (n * k) * (15 * body.length + 12 * n + 31) + 1,
      phaseBInnerLoopProg.Exec (phaseBInnerStore n k body q 0)
        (phaseBInnerStore n k body q (n * k)) c := by
  refine exec_bounded_loop (fun h => (h .Krem).isSome) phaseBInnerBodyProg (n * k)
    (phaseBInnerStore n k body q) (15 * body.length + 12 * n + 29) ?_ ?_ ?_
  · intro idx hidx
    simp [phaseBInnerStore, head?_replicate_isSome, Nat.sub_pos_of_lt hidx]
  · simp [phaseBInnerStore]
  · intro idx _
    set s0 := phaseBInnerStore n k body q idx
    have hp1 := (stack_basic_macros SKey.Krem s0).2.1
    set s1 := Function.update s0 .Krem (s0 .Krem).tail
    have e1 : ∃ c ≤ 1, (popProg .Krem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
    have e2 := exec_readUnaryProg_wordAt .W .V0 (by decide) s1 body idx
      (by simp [s1, s0, phaseBInnerStore]) (by simp [s1, s0, phaseBInnerStore])
    set s2 := Function.update (Function.update s1 .W (wordAt body (idx + 1)))
      .V0 (List.replicate (valAt body idx) (some true))
    set s3_target := Function.update s2 .Found
      (if isSourceUpTo body (sinkValUpTo k body n) q (idx + 1) then [] else [some true])
    have hv_le : valAt body idx ≤ body.length := valAt_le_length body idx
    have e3 : ∃ c ≤ 9 * body.length + 12 * n + 21,
        (branchEqVQ (.seq (clearProg .Found) (pushProg .Found (some true))) (popProg .sc)).Exec
          s2 s3_target c := by
      by_cases hvq : valAt body idx = q
      · have hc_f := (stack_basic_macros SKey.Found s2).2.2
        set sf1 := Function.update s2 .Found []
        have ef1 : ∃ c ≤ 4, (clearProg .Found).Exec s2 sf1 c := by
          refine ⟨3 * (s2 .Found).length + 1, ?_, hc_f⟩
          simp [s2, s1, s0, phaseBInnerStore]
          split_ifs <;> simp
        have hp_f := (stack_basic_macros SKey.Found sf1).1 (some true)
        have ef2 : ∃ c ≤ 1, (pushProg .Found (some true)).Exec sf1 s3_target c := by
          refine ⟨1, le_rfl, exec_congr hp_f ?_⟩
          funext j
          cases j <;> simp [sf1, s3_target, s2, isSourceUpTo_succ, hvq]
        have e_br := exec_branchEqVQ_true
          (.seq (clearProg .Found) (pushProg .Found (some true))) (popProg .sc)
          s2 s3_target (valAt body idx) q (4 + 1 + 1)
          (by simp [s2]) (by simp [s2, s1, s0, phaseBInnerStore])
          (by simp [s2, s1, s0, phaseBInnerStore]) (by simp [s2, s1, s0, phaseBInnerStore])
          (by simp [s2, s1, s0, phaseBInnerStore]) hvq (exec_seq_le ef1 ef2)
        exact exec_le_of_le e_br (by omega)
      · have hpop := (stack_basic_macros SKey.sc s2).2.1
        have ef : ∃ c ≤ 1, (popProg .sc).Exec s2 s3_target c := by
          refine ⟨1, le_rfl, exec_congr hpop ?_⟩
          funext j
          cases j <;> simp [s3_target, s2, s1, s0, phaseBInnerStore, isSourceUpTo_succ, hvq]
        have e_br := exec_branchEqVQ_false
          (.seq (clearProg .Found) (pushProg .Found (some true))) (popProg .sc)
          s2 s3_target (valAt body idx) q 1
          (by simp [s2]) (by simp [s2, s1, s0, phaseBInnerStore])
          (by simp [s2, s1, s0, phaseBInnerStore]) (by simp [s2, s1, s0, phaseBInnerStore])
          (by simp [s2, s1, s0, phaseBInnerStore]) hvq ef
        exact exec_le_of_le e_br (by omega)
    have hc4 := (stack_basic_macros SKey.V0 s3_target).2.2
    have e4 : ∃ c ≤ 3 * body.length + 1,
        (clearProg .V0).Exec s3_target (phaseBInnerStore n k body q (idx + 1)) c := by
      refine ⟨3 * (s3_target .V0).length + 1, ?_, exec_congr hc4 ?_⟩
      · simp [s3_target, s2]
        omega
      · funext j
        cases j <;> simp [s3_target, s2, s1, s0, phaseBInnerStore, Nat.sub_sub]
    have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))
    exact exec_le_of_le e_all (by omega)

lemma exec_phaseBBodyProg (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ (n * k) * (15 * body.length + 12 * n + 31) + 6 * (n * k) + 9 * body.length + 27 * n + 42,
      phaseBBodyProg.Exec (phaseBStore n k body q) (phaseBStore n k body (q + 1)) c := by
  set s0 := phaseBStore n k body q
  have hp1 := (stack_basic_macros SKey.Nrem s0).2.1
  set s1 := Function.update s0 .Nrem (s0 .Nrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Nrem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have hc2 := stack_copy SKey.ki SKey.W SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, s0, phaseBStore])
  set s2 := Function.update s1 .W (s1 .ki ++ s1 .W)
  have e2 : ∃ c ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s1 s2 c :=
    ⟨6 * (s1 .ki).length + 3, by simp [s1, s0, phaseBStore], hc2⟩
  have hc3 := stack_copy SKey.NK SKey.Krem SKey.sc (by decide) (by decide) (by decide) s2
    (by simp [s2, s1, s0, phaseBStore])
  set s3 := Function.update (phaseBInnerStore n k body q 0) .Found []
  have e3 : ∃ c ≤ 6 * (n * k) + 3, (copyProg .NK .Krem .sc).Exec s2 s3 c := by
    refine ⟨6 * (s2 .NK).length + 3, by simp [s2, s1, s0, phaseBStore], exec_congr hc3 ?_⟩
    funext j
    cases j <;> simp [s3, s2, s1, s0, phaseBStore, phaseBInnerStore, wordAt, Nat.sub_sub]
  have e3b : ∃ c ≤ 21 * n + 16,
      (branchEqQF (pushProg .Found (some true)) (popProg .sc)).Exec s3 (phaseBInnerStore n k body q 0) c := by
    have hf_le := sinkValUpTo_le k body n
    by_cases hqf : q = sinkValUpTo k body n
    · have he : ∃ c ≤ 1, (pushProg .Found (some true)).Exec s3 (phaseBInnerStore n k body q 0) c := by
        refine ⟨1, le_rfl, exec_congr ((stack_basic_macros SKey.Found s3).1 (some true)) ?_⟩
        funext j
        cases j <;> simp [s3, phaseBInnerStore, isSourceUpTo, hqf]
      exact exec_le_of_le (exec_branchEqQF_true _ _ s3 _ q (sinkValUpTo k body n) 1
        (by simp [s3, phaseBInnerStore]) (by simp [s3, phaseBInnerStore])
        (by simp [s3, phaseBInnerStore]) (by simp [s3, phaseBInnerStore])
        (by simp [s3, phaseBInnerStore]) hqf he) (by omega)
    · have he : ∃ c ≤ 1, (popProg .sc).Exec s3 (phaseBInnerStore n k body q 0) c := by
        refine ⟨1, le_rfl, exec_congr (stack_basic_macros SKey.sc s3).2.1 ?_⟩
        funext j
        cases j <;> simp [s3, phaseBInnerStore, isSourceUpTo, hqf]
      exact exec_le_of_le (exec_branchEqQF_false _ _ s3 _ q (sinkValUpTo k body n) 1
        (by simp [s3, phaseBInnerStore]) (by simp [s3, phaseBInnerStore])
        (by simp [s3, phaseBInnerStore]) (by simp [s3, phaseBInnerStore])
        (by simp [s3, phaseBInnerStore]) hqf he) (by omega)
  have e4 := exec_phaseBInnerLoopProg n k body q hq
  set s4 := phaseBInnerStore n k body q (n * k)
  have hc5 := (stack_basic_macros SKey.W s4).2.2
  set s5 := Function.update s4 .W []
  have hw_le : (wordAt body (n * k)).length ≤ body.length := length_wordAt_le body (n * k)
  have e5 : ∃ c ≤ 3 * body.length + 1, (clearProg .W).Exec s4 s5 c := by
    refine ⟨3 * (s4 .W).length + 1, ?_, hc5⟩
    simp [s4, phaseBInnerStore]
    omega
  set s6_target := Function.update (phaseBStore n k body (q + 1)) .Q (List.replicate q (some true))
  have hlen_le : (sourceValsUpTo n k body q).length ≤ q := length_sourceValsUpTo_le n k body q
  have e6 : ∃ c ≤ 6 * n + 8,
      (StackProg.branch (fun h => (h .Found).isNone)
        (.seq (emitUnaryTo .Q .Srev) (pushProg .Scnt (some true)))
        (.seq (clearProg .Found) (pushProg .D (some true)))).Exec s5 s6_target c := by
    cases hsrc : isSourceVal n k body q
    · have hsrc' : isSourceUpTo body (sinkValUpTo k body n) q (n * k) = false := hsrc
      have htest : (fun h : SKey → Option Sym => (h .Found).isNone) (fun j => (s5 j).head?) = false := by
        show (s5 .Found).head?.isNone = false
        simp [s5, s4, phaseBInnerStore, hsrc']
      have hcf := (stack_basic_macros SKey.Found s5).2.2
      set sf1 := Function.update s5 .Found []
      have ef1 : ∃ c ≤ 4, (clearProg .Found).Exec s5 sf1 c := by
        refine ⟨3 * (s5 .Found).length + 1, ?_, hcf⟩
        simp [s5, s4, phaseBInnerStore]
        split_ifs <;> simp
      have hpd := (stack_basic_macros SKey.D sf1).1 (some true)
      have hsub_eq : q + 1 - (sourceValsUpTo n k body q).length =
          (q - (sourceValsUpTo n k body q).length) + 1 := by omega
      have ef2 : ∃ c ≤ 1, (pushProg .D (some true)).Exec sf1 s6_target c := by
        refine ⟨1, le_rfl, exec_congr hpd ?_⟩
        funext j
        cases j <;> simp [sf1, s5, s4, s6_target, phaseBInnerStore, phaseBStore,
          sourceValsUpTo_succ_of_false n k body q hsrc, hsrc', hsub_eq, List.replicate_succ]
      exact exec_le_of_le
        (exec_branch_false_le (fun h => (h .Found).isNone) _ _ htest (exec_seq_le ef1 ef2))
        (by omega)
    · have hsrc' : isSourceUpTo body (sinkValUpTo k body n) q (n * k) = true := hsrc
      have htest : (fun h : SKey → Option Sym => (h .Found).isNone) (fun j => (s5 j).head?) = true := by
        show (s5 .Found).head?.isNone = true
        simp [s5, s4, phaseBInnerStore, hsrc']
      have et1 := exec_emitUnaryTo .Q .Srev (by decide) (by decide) (by decide) s5 q
        (by simp [s5, s4, phaseBInnerStore]) (by simp [s5, s4, phaseBInnerStore])
      set st1 := Function.update s5 .Srev ((encUnary q).reverse ++ s5 .Srev)
      have hps := (stack_basic_macros SKey.Scnt st1).1 (some true)
      have et2 : ∃ c ≤ 1, (pushProg .Scnt (some true)).Exec st1 s6_target c := by
        refine ⟨1, le_rfl, exec_congr hps ?_⟩
        funext j
        cases j <;> simp [st1, s5, s4, s6_target, phaseBInnerStore, phaseBStore,
          sourceValsUpTo_succ_of_true n k body q hsrc, hsrc',
          List.replicate_succ, List.reverse_append]
      exact exec_le_of_le
        (exec_branch_true_le (fun h => (h .Found).isNone) _ _ htest (exec_seq_le et1 et2))
        (by omega)
  have hp7 := (stack_basic_macros SKey.Q s6_target).1 (some true)
  have e7 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec s6_target (phaseBStore n k body (q + 1)) c := by
    refine ⟨1, le_rfl, exec_congr hp7 ?_⟩
    funext j
    cases j <;> simp [s6_target, phaseBStore, List.replicate_succ]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3
    (exec_seq_le (exec_seq_le e3b e4) (exec_seq_le e5 (exec_seq_le e6 e7)))))
  exact exec_le_of_le e_all (by omega)

lemma exec_phaseBLoopProg (n k : ℕ) (body : List Sym) :
    let B := (n * k) * (15 * body.length + 12 * n + 31) + 6 * (n * k) + 9 * body.length + 27 * n + 42
    ∃ c ≤ n * (B + 2) + 1,
      phaseBLoopProg.Exec (phaseBStore n k body 0) (phaseBStore n k body n) c := by
  intro _B
  refine exec_bounded_loop (fun h => (h .Nrem).isSome) phaseBBodyProg n
    (phaseBStore n k body) _ ?_ ?_ ?_
  · intro q hq
    simp [phaseBStore, head?_replicate_isSome, Nat.sub_pos_of_lt hq]
  · simp [phaseBStore]
  · intro q hq
    exact exec_phaseBBodyProg n k body q hq

/-! ### Stage 2B.4: Phase C (`phaseBToCProg`, `phaseC1LoopProg`, `phaseC2LoopProg`) -/

lemma fkPart_zero (f_val : ℕ) : fkPart f_val 0 = [] := rfl

lemma fkPart_succ (f_val a : ℕ) :
    fkPart f_val (a + 1) = fkPart f_val a ++ encUnary f_val := by
  simp [fkPart, List.range_succ]

def emitFKBodyProg : Prog :=
  .seq (popProg .Krem) (emitUnaryTo .F .outRev)

def emitFKLoopProg : Prog :=
  .loop (fun h => (h .Krem).isSome) emitFKBodyProg

def emitFKTimesProg : Prog :=
  .seq (copyProg .K .Krem .sc) emitFKLoopProg

def sEmitFK (s : Store) (k f_val a : ℕ) : Store :=
  Function.update (Function.update s .Krem (List.replicate (k - a) (some true)))
    .outRev ((fkPart f_val a).reverse ++ s .outRev)

lemma exec_emitFKTimesProg (s : Store) (n k f_val : ℕ)
    (hK : s .K = List.replicate k (some true))
    (hKrem : s .Krem = [])
    (hF : s .F = List.replicate f_val (some true))
    (hsc : s .sc = [])
    (hf_le : f_val ≤ n) :
    ∃ c ≤ k * (6 * n + 9) + 6 * k + 5,
      emitFKTimesProg.Exec s
        (Function.update s .outRev ((fkPart f_val k).reverse ++ s .outRev)) c := by
  have hc1 := stack_copy SKey.K SKey.Krem SKey.sc (by decide) (by decide) (by decide) s hsc
  have e1 : ∃ c ≤ 6 * k + 3, (copyProg .K .Krem .sc).Exec s (sEmitFK s k f_val 0) c := by
    refine ⟨6 * (s .K).length + 3, by simp [hK], exec_congr hc1 ?_⟩
    funext j
    cases j <;> simp [sEmitFK, fkPart_zero, hK, hKrem]
  have hloop := exec_bounded_loop (fun h => (h .Krem).isSome) emitFKBodyProg k
    (sEmitFK s k f_val) (6 * n + 7)
    (fun a ha => by
      show (sEmitFK s k f_val a .Krem).head?.isSome = true
      simp [sEmitFK, head?_replicate_isSome, Nat.sub_pos_of_lt ha])
    (by
      show (sEmitFK s k f_val k .Krem).head?.isSome = false
      simp [sEmitFK])
    (fun a _ => by
      set s0 := sEmitFK s k f_val a
      have hp1 := (stack_basic_macros SKey.Krem s0).2.1
      set s1 := Function.update s0 .Krem (s0 .Krem).tail
      have ep1 : ∃ c ≤ 1, (popProg .Krem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
      have ep2 := exec_emitUnaryTo .F .outRev (by decide) (by decide) (by decide) s1 f_val
        (by simp [s1, s0, sEmitFK, hF]) (by simp [s1, s0, sEmitFK, hsc])
      have ep2' : ∃ c ≤ 6 * f_val + 5,
          (emitUnaryTo .F .outRev).Exec s1 (sEmitFK s k f_val (a + 1)) c := by
        rcases ep2 with ⟨c2, hc2, ec2⟩
        refine ⟨c2, hc2, exec_congr ec2 ?_⟩
        funext j
        cases j <;> simp [s1, s0, sEmitFK, fkPart_succ, List.reverse_append, Nat.sub_sub]
      exact exec_le_of_le (exec_seq_le ep1 ep2') (by omega))
  rcases hloop with ⟨c2, hc2, eloop⟩
  have e2 : ∃ c ≤ k * (6 * n + 9) + 1,
      emitFKLoopProg.Exec (sEmitFK s k f_val 0)
        (Function.update s .outRev ((fkPart f_val k).reverse ++ s .outRev)) c := by
    refine ⟨c2, hc2, exec_congr eloop ?_⟩
    funext j
    cases j <;> simp [sEmitFK, hKrem]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

lemma phaseC1Table_zero (n k f_val : ℕ) : phaseC1Table n k f_val 0 = [] := rfl

lemma phaseC1Table_succ (n k f_val i : ℕ) :
    phaseC1Table n k f_val (i + 1) = phaseC1Table n k f_val i ++ phaseC1Row n k f_val i := by
  simp [phaseC1Table, List.range_succ]

def phaseC1Store (n k : ℕ) (body : List Sym) (i : ℕ) : Store :=
  let f_val := sinkValUpTo k body n
  let S_list := sourceValsUpTo n k body n
  let d := n - S_list.length
  fun j =>
    match j with
    | .ki => body
    | .N => List.replicate n (some true)
    | .K => List.replicate k (some true)
    | .K2 => List.replicate (k + 2) (some true)
    | .NK => List.replicate (n * k) (some true)
    | .Nrem => List.replicate (n - i) (some true)
    | .Q => List.replicate (n + i) (some true)
    | .F => List.replicate f_val (some true)
    | .D => List.replicate (d - i) (some true)
    | .Scnt => List.replicate S_list.length (some true)
    | .S => S_list.flatMap encUnary
    | .outRev =>
        (phaseC1Table n k f_val i).reverse ++
          (phaseATable n k body n).reverse ++ headerRev n k
    | _ => []

lemma length_flatMap_encUnary_sourceValsUpTo (n k : ℕ) (body : List Sym) :
    ∀ q ≤ n, ((sourceValsUpTo n k body q).flatMap encUnary).length ≤ q * (n + 1)
  | 0, _ => by simp [sourceValsUpTo]
  | q + 1, hq => by
    have ih := length_flatMap_encUnary_sourceValsUpTo n k body q (by omega)
    rw [Nat.succ_mul]
    cases h : isSourceVal n k body q
    · rw [sourceValsUpTo_succ_of_false n k body q h]
      omega
    · rw [sourceValsUpTo_succ_of_true n k body q h]
      simp only [List.flatMap_append, List.flatMap_singleton, List.length_append,
        encUnary, List.length_replicate, List.length_singleton]
      omega

def phaseBToCProg : Prog :=
  .seq (transferProg .Srev (fun j => decide (j = .S)))
    (copyProg .N .Nrem .sc)

lemma exec_phaseBToCProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 3 * (n * n) + 9 * n + 5,
      phaseBToCProg.Exec (phaseBStore n k body n) (phaseC1Store n k body 0) c := by
  set s0 := phaseBStore n k body n
  have ht1 := stack_transfer SKey.Srev (fun j => decide (j = .S)) s0
  set s1 := transferStore .Srev (fun j => decide (j = .S)) s0
  have hlen_srev : (s0 .Srev).length ≤ n * n + n := by
    simp only [s0, phaseBStore, List.length_reverse]
    have h := length_flatMap_encUnary_sourceValsUpTo n k body n le_rfl
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have e1 : ∃ c ≤ 3 * (n * n) + 3 * n + 1,
      (transferProg .Srev (fun j => decide (j = .S))).Exec s0 s1 c :=
    ⟨3 * (s0 .Srev).length + 1, by omega, ht1⟩
  have hc2 := stack_copy SKey.N SKey.Nrem SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, transferStore, s0, phaseBStore])
  have e2 : ∃ c ≤ 6 * n + 3,
      (copyProg .N .Nrem .sc).Exec s1 (phaseC1Store n k body 0) c := by
    refine ⟨6 * (s1 .N).length + 3, by simp [s1, transferStore, s0, phaseBStore],
      exec_congr hc2 ?_⟩
    funext j
    cases j <;> simp [s1, transferStore, s0, phaseBStore, phaseC1Store, phaseC1Table_zero]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

def phaseC1BodyProg : Prog :=
  .seq (popProg .D)
    (.seq (popProg .Nrem)
      (.seq (pushProg .Q (some true))
        (.seq emitFKTimesProg
          (.branch (fun h => (h .Nrem).isSome)
            (.seq (emitUnaryTo .Q .outRev) (emitUnaryTo .Q .outRev))
            (.seq (emitUnaryTo .F .outRev) (emitUnaryTo .F .outRev))))))

def phaseC1LoopProg : Prog :=
  .loop (fun h => (h .D).isSome) phaseC1BodyProg

lemma exec_phaseC1BodyProg (n k : ℕ) (body : List Sym) (i : ℕ)
    (hi : i < n - (sourceValsUpTo n k body n).length) :
    ∃ c ≤ k * (6 * n + 9) + 6 * k + 24 * n + 24,
      phaseC1BodyProg.Exec (phaseC1Store n k body i) (phaseC1Store n k body (i + 1)) c := by
  set f_val := sinkValUpTo k body n
  have hf_le : f_val ≤ n := sinkValUpTo_le k body n
  have hi_n : i < n := by omega
  set s0 := phaseC1Store n k body i
  have hp1 := (stack_basic_macros SKey.D s0).2.1
  set s1 := Function.update s0 .D (s0 .D).tail
  have e1 : ∃ c ≤ 1, (popProg .D).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have hp2 := (stack_basic_macros SKey.Nrem s1).2.1
  set s2 := Function.update s1 .Nrem (s1 .Nrem).tail
  have e2 : ∃ c ≤ 1, (popProg .Nrem).Exec s1 s2 c := ⟨1, le_rfl, hp2⟩
  have hp3 := (stack_basic_macros SKey.Q s2).1 (some true)
  set s3 := Function.update s2 .Q (some true :: s2 .Q)
  have e3 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec s2 s3 c := ⟨1, le_rfl, hp3⟩
  have e4 := exec_emitFKTimesProg s3 n k f_val
    (by simp [s3, s2, s1, s0, phaseC1Store])
    (by simp [s3, s2, s1, s0, phaseC1Store])
    (by simp [s3, s2, s1, s0, phaseC1Store, f_val])
    (by simp [s3, s2, s1, s0, phaseC1Store])
    hf_le
  set s4 := Function.update s3 .outRev ((fkPart f_val k).reverse ++ s3 .outRev)
  have hD_eq : n - ((sourceValsUpTo n k body n).length + i + 1) =
      n - ((sourceValsUpTo n k body n).length + (i + 1)) := by omega
  have hQ_eq : some true :: List.replicate (n + i) (some true) =
      List.replicate (n + (i + 1)) (some true) := by
    rw [show n + (i + 1) = (n + i) + 1 by omega, List.replicate_succ]
  have hs4_Q : s4 .Q = List.replicate (n + (i + 1)) (some true) := by
    simp [s4, s3, s2, s1, s0, phaseC1Store, hQ_eq]
  have hs4_Nrem : s4 .Nrem = List.replicate (n - (i + 1)) (some true) := by
    simp [s4, s3, s2, s1, s0, phaseC1Store, Nat.sub_sub]
  have e5 : ∃ c ≤ 24 * n + 12,
      (StackProg.branch (fun h => (h .Nrem).isSome)
        (.seq (emitUnaryTo .Q .outRev) (emitUnaryTo .Q .outRev))
        (.seq (emitUnaryTo .F .outRev) (emitUnaryTo .F .outRev))).Exec
        s4 (phaseC1Store n k body (i + 1)) c := by
    by_cases hnext : i + 1 < n
    · have htest : (fun h : SKey → Option Sym => (h .Nrem).isSome) (fun j => (s4 j).head?) = true := by
        show (s4 .Nrem).head?.isSome = true
        rw [hs4_Nrem]
        exact head?_replicate_isSome _ _ (by omega)
      have et1 := exec_emitUnaryTo .Q .outRev (by decide) (by decide) (by decide) s4 (n + (i + 1))
        hs4_Q (by simp [s4, s3, s2, s1, s0, phaseC1Store])
      set st1 := Function.update s4 .outRev ((encUnary (n + (i + 1))).reverse ++ s4 .outRev)
      have et2 := exec_emitUnaryTo .Q .outRev (by decide) (by decide) (by decide) st1 (n + (i + 1))
        (by simp [st1, hs4_Q]) (by simp [st1, s4, s3, s2, s1, s0, phaseC1Store])
      have et2' : ∃ c ≤ 6 * (n + (i + 1)) + 5,
          (emitUnaryTo .Q .outRev).Exec st1 (phaseC1Store n k body (i + 1)) c := by
        rcases et2 with ⟨c2, hc2, ec2⟩
        refine ⟨c2, hc2, exec_congr ec2 ?_⟩
        funext j
        cases j <;> simp [st1, s4, s3, s2, s1, s0, phaseC1Store, hD_eq, hQ_eq, hs4_Q, hs4_Nrem,
          phaseC1Table_succ, phaseC1Row, phaseC1ExtraVal, hnext, f_val,
          Nat.sub_sub, List.reverse_append]
      exact exec_le_of_le
        (exec_branch_true_le (fun h => (h .Nrem).isSome) _ _ htest (exec_seq_le et1 et2'))
        (by omega)
    · have htest : (fun h : SKey → Option Sym => (h .Nrem).isSome) (fun j => (s4 j).head?) = false := by
        show (s4 .Nrem).head?.isSome = false
        have hzero : n - (i + 1) = 0 := by omega
        rw [hs4_Nrem, hzero]
        rfl
      have ef1 := exec_emitUnaryTo .F .outRev (by decide) (by decide) (by decide) s4 f_val
        (by simp [s4, s3, s2, s1, s0, phaseC1Store, f_val])
        (by simp [s4, s3, s2, s1, s0, phaseC1Store])
      set sf1 := Function.update s4 .outRev ((encUnary f_val).reverse ++ s4 .outRev)
      have ef2 := exec_emitUnaryTo .F .outRev (by decide) (by decide) (by decide) sf1 f_val
        (by simp [sf1, s4, s3, s2, s1, s0, phaseC1Store, f_val])
        (by simp [sf1, s4, s3, s2, s1, s0, phaseC1Store])
      have ef2' : ∃ c ≤ 6 * f_val + 5,
          (emitUnaryTo .F .outRev).Exec sf1 (phaseC1Store n k body (i + 1)) c := by
        rcases ef2 with ⟨c2, hc2, ec2⟩
        refine ⟨c2, hc2, exec_congr ec2 ?_⟩
        funext j
        cases j <;> simp [sf1, s4, s3, s2, s1, s0, phaseC1Store, hD_eq, hQ_eq, hs4_Q, hs4_Nrem,
          phaseC1Table_succ, phaseC1Row, phaseC1ExtraVal, hnext, f_val,
          Nat.sub_sub, List.reverse_append]
      exact exec_le_of_le
        (exec_branch_false_le (fun h => (h .Nrem).isSome) _ _ htest (exec_seq_le ef1 ef2'))
        (by omega)
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 e5)))
  exact exec_le_of_le e_all (by omega)

lemma exec_phaseC1LoopProg (n k : ℕ) (body : List Sym) :
    let d := n - (sourceValsUpTo n k body n).length
    let B := k * (6 * n + 9) + 6 * k + 24 * n + 24
    ∃ c ≤ n * (B + 2) + 1,
      phaseC1LoopProg.Exec (phaseC1Store n k body 0) (phaseC1Store n k body d) c := by
  intro d B
  have hloop := exec_bounded_loop (fun h => (h .D).isSome) phaseC1BodyProg d
    (phaseC1Store n k body) B
    (fun i hi => by
      simp [phaseC1Store, d, head?_replicate_isSome, Nat.sub_pos_of_lt hi])
    (by simp [phaseC1Store, d])
    (fun i hi => exec_phaseC1BodyProg n k body i hi)
  have hd_le : d * (B + 2) ≤ n * (B + 2) := Nat.mul_le_mul_right (B + 2) (Nat.sub_le _ _)
  exact exec_le_of_le hloop (by omega)

lemma phaseC2Table_zero (n k f_val : ℕ) (S_list : List ℕ) (d : ℕ) :
    phaseC2Table n k f_val S_list d 0 = [] := rfl

lemma phaseC2Table_succ (n k f_val : ℕ) (S_list : List ℕ) (d j : ℕ) :
    phaseC2Table n k f_val S_list d (j + 1) =
      phaseC2Table n k f_val S_list d j ++ phaseC2Row n k f_val S_list d j := by
  simp [phaseC2Table, List.range_succ]

def phaseC2Store (n k : ℕ) (body : List Sym) (j : ℕ) : Store :=
  let f_val := sinkValUpTo k body n
  let S_list := sourceValsUpTo n k body n
  let d := n - S_list.length
  fun key =>
    match key with
    | .ki => body
    | .N => List.replicate n (some true)
    | .K => List.replicate k (some true)
    | .K2 => List.replicate (k + 2) (some true)
    | .NK => List.replicate (n * k) (some true)
    | .Nrem => List.replicate (n - (d + j)) (some true)
    | .Q => List.replicate (n + (d + j)) (some true)
    | .F => List.replicate f_val (some true)
    | .Scnt => List.replicate (S_list.length - j) (some true)
    | .S => (S_list.drop j).flatMap encUnary
    | .outRev =>
        (phaseC2Table n k f_val S_list d j).reverse ++
          (phaseC1Table n k f_val d).reverse ++
          (phaseATable n k body n).reverse ++ headerRev n k
    | _ => []

lemma leadOnes_replicate_append (n : ℕ) (xs : List Sym) :
    leadOnes (List.replicate n (some true) ++ none :: xs) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, leadOnes, ih]

lemma nextWord_replicate_append (n : ℕ) (xs : List Sym) :
    nextWord (List.replicate n (some true) ++ none :: xs) = xs := by
  unfold nextWord
  rw [leadOnes_replicate_append]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

lemma drop_flatMap_encUnary :
    ∀ (L : List ℕ) (j : ℕ), j < L.length →
      (L.drop j).flatMap encUnary =
        List.replicate (L.getD j 0) (some true) ++ none :: (L.drop (j + 1)).flatMap encUnary
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: xs, 0, _ => by
    simp [encUnary]
  | _ :: xs, j + 1, hj => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
    simpa [List.drop_succ_cons] using drop_flatMap_encUnary xs j hj

lemma exec_readUnaryProg_flatMap (src dst : SKey) (hsd : src ≠ dst)
    (s : Store) (L : List ℕ) (j n : ℕ) (hj : j < L.length) (h_le : L.getD j 0 ≤ n)
    (hsrc : s src = (L.drop j).flatMap encUnary) (hdst : s dst = []) :
    ∃ c ≤ 3 * n + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src ((L.drop (j + 1)).flatMap encUnary))
          dst (List.replicate (L.getD j 0) (some true))) c := by
  have hraw := exec_readUnaryProg_raw src dst hsd s hdst
  have h_eq := drop_flatMap_encUnary L j hj
  have h_lead : leadOnes (s src) = L.getD j 0 := by
    rw [hsrc, h_eq, leadOnes_replicate_append]
  have h_next : nextWord (s src) = (L.drop (j + 1)).flatMap encUnary := by
    rw [hsrc, h_eq, nextWord_replicate_append]
  rw [h_lead, h_next] at hraw
  exact exec_le_of_le hraw (by omega)

def phaseC2BodyProg : Prog :=
  .seq (popProg .Scnt)
    (.seq (popProg .Nrem)
      (.seq (pushProg .Q (some true))
        (.seq (readUnaryProg .S .V0)
          (.seq emitFKTimesProg
            (.seq (emitUnaryTo .V0 .outRev)
              (.seq (.branch (fun h => (h .Nrem).isSome)
                  (emitUnaryTo .Q .outRev)
                  (emitUnaryTo .V0 .outRev))
                (clearProg .V0)))))))

def phaseC2LoopProg : Prog :=
  .loop (fun h => (h .Scnt).isSome) phaseC2BodyProg

lemma exec_phaseC2BodyProg (n k : ℕ) (body : List Sym) (j : ℕ)
    (hj : j < (sourceValsUpTo n k body n).length) :
    ∃ c ≤ k * (6 * n + 9) + 6 * k + 24 * n + 30,
      phaseC2BodyProg.Exec (phaseC2Store n k body j) (phaseC2Store n k body (j + 1)) c := by
  set f_val := sinkValUpTo k body n
  set S_list := sourceValsUpTo n k body n
  set d := n - S_list.length
  set s_val := S_list.getD j 0
  have hf_le : f_val ≤ n := sinkValUpTo_le k body n
  have hs_le : s_val ≤ n := getD_sourceValsUpTo_le n k body n j
  have hlen_le : S_list.length ≤ n := length_sourceValsUpTo_le n k body n
  have hdj_lt : d + j < n := by omega
  set s0 := phaseC2Store n k body j
  have hp1 := (stack_basic_macros SKey.Scnt s0).2.1
  set s1 := Function.update s0 .Scnt (s0 .Scnt).tail
  have e1 : ∃ c ≤ 1, (popProg .Scnt).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have hp2 := (stack_basic_macros SKey.Nrem s1).2.1
  set s2 := Function.update s1 .Nrem (s1 .Nrem).tail
  have e2 : ∃ c ≤ 1, (popProg .Nrem).Exec s1 s2 c := ⟨1, le_rfl, hp2⟩
  have hp3 := (stack_basic_macros SKey.Q s2).1 (some true)
  set s3 := Function.update s2 .Q (some true :: s2 .Q)
  have e3 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec s2 s3 c := ⟨1, le_rfl, hp3⟩
  have e4 := exec_readUnaryProg_flatMap .S .V0 (by decide) s3 S_list j n hj hs_le
    (by simp [s3, s2, s1, s0, phaseC2Store, S_list])
    (by simp [s3, s2, s1, s0, phaseC2Store])
  set s4 := Function.update (Function.update s3 .S ((S_list.drop (j + 1)).flatMap encUnary))
    .V0 (List.replicate s_val (some true))
  have e5 := exec_emitFKTimesProg s4 n k f_val
    (by simp [s4, s3, s2, s1, s0, phaseC2Store])
    (by simp [s4, s3, s2, s1, s0, phaseC2Store])
    (by simp [s4, s3, s2, s1, s0, phaseC2Store, f_val])
    (by simp [s4, s3, s2, s1, s0, phaseC2Store])
    hf_le
  set s5 := Function.update s4 .outRev ((fkPart f_val k).reverse ++ s4 .outRev)
  have e6 := exec_emitUnaryTo .V0 .outRev (by decide) (by decide) (by decide) s5 s_val
    (by simp [s5, s4])
    (by simp [s5, s4, s3, s2, s1, s0, phaseC2Store])
  set s6 := Function.update s5 .outRev ((encUnary s_val).reverse ++ s5 .outRev)
  have hQ_eq : some true :: List.replicate (n + (n - (sourceValsUpTo n k body n).length + j)) (some true) =
      List.replicate (n + (n - (sourceValsUpTo n k body n).length + (j + 1))) (some true) := by
    rw [show n + (n - (sourceValsUpTo n k body n).length + (j + 1)) =
      (n + (n - (sourceValsUpTo n k body n).length + j)) + 1 by omega, List.replicate_succ]
  have hs6_Q : s6 .Q = List.replicate (n + (d + (j + 1))) (some true) := by
    simp [s6, s5, s4, s3, s2, s1, s0, phaseC2Store, d, S_list, hQ_eq]
  have hs6_Nrem : s6 .Nrem = List.replicate (n - (d + j + 1)) (some true) := by
    simp [s6, s5, s4, s3, s2, s1, s0, phaseC2Store, d, S_list, Nat.sub_sub]
  set s7_target := Function.update s6 .outRev
    ((encUnary (phaseC2ExtraVal n s_val (d + j))).reverse ++ s6 .outRev)
  have e7 : ∃ c ≤ 12 * n + 6,
      (StackProg.branch (fun h => (h .Nrem).isSome)
        (emitUnaryTo .Q .outRev)
        (emitUnaryTo .V0 .outRev)).Exec s6 s7_target c := by
    by_cases hnext : d + j + 1 < n
    · have htest : (fun h : SKey → Option Sym => (h .Nrem).isSome) (fun key => (s6 key).head?) = true := by
        show (s6 .Nrem).head?.isSome = true
        rw [hs6_Nrem]
        exact head?_replicate_isSome _ _ (by omega)
      have et := exec_emitUnaryTo .Q .outRev (by decide) (by decide) (by decide) s6 (n + (d + (j + 1)))
        hs6_Q (by simp [s6, s5, s4, s3, s2, s1, s0, phaseC2Store])
      have et' : ∃ c ≤ 6 * (n + (d + (j + 1))) + 5,
          (emitUnaryTo .Q .outRev).Exec s6 s7_target c := by
        rcases et with ⟨ct, hct, ect⟩
        refine ⟨ct, hct, exec_congr ect ?_⟩
        have hextra : phaseC2ExtraVal n s_val (d + j) = n + (d + (j + 1)) := by
          unfold phaseC2ExtraVal
          rw [if_pos hnext, Nat.add_assoc]
        funext key
        cases key <;> simp [s7_target, hextra]
      exact exec_le_of_le
        (exec_branch_true_le (fun h => (h .Nrem).isSome) _ _ htest et')
        (by omega)
    · have htest : (fun h : SKey → Option Sym => (h .Nrem).isSome) (fun key => (s6 key).head?) = false := by
        show (s6 .Nrem).head?.isSome = false
        have hzero : n - (d + j + 1) = 0 := by omega
        rw [hs6_Nrem, hzero]
        rfl
      have ef := exec_emitUnaryTo .V0 .outRev (by decide) (by decide) (by decide) s6 s_val
        (by simp [s6, s5, s4])
        (by simp [s6, s5, s4, s3, s2, s1, s0, phaseC2Store])
      have ef' : ∃ c ≤ 6 * s_val + 5,
          (emitUnaryTo .V0 .outRev).Exec s6 s7_target c := by
        rcases ef with ⟨cf, hcf, ecf⟩
        refine ⟨cf, hcf, exec_congr ecf ?_⟩
        funext key
        cases key <;> simp [s7_target, phaseC2ExtraVal, hnext]
      exact exec_le_of_le
        (exec_branch_false_le (fun h => (h .Nrem).isSome) _ _ htest ef')
        (by omega)
  have hc8 := (stack_basic_macros SKey.V0 s7_target).2.2
  have e8 : ∃ c ≤ 3 * n + 1,
      (clearProg .V0).Exec s7_target (phaseC2Store n k body (j + 1)) c := by
    refine ⟨3 * (s7_target .V0).length + 1, ?_, exec_congr hc8 ?_⟩
    · simp [s7_target, s6, s5, s4]
      omega
    · funext key
      cases key <;> simp [s7_target, s6, s5, s4, s3, s2, s1, s0, phaseC2Store,
        hQ_eq, hs6_Q, hs6_Nrem, phaseC2Table_succ, phaseC2Row, f_val, S_list, d, s_val,
        Nat.sub_sub, Nat.add_assoc, List.reverse_append]
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4
    (exec_seq_le e5 (exec_seq_le e6 (exec_seq_le e7 e8))))))
  exact exec_le_of_le e_all (by omega)

lemma exec_phaseC2LoopProg (n k : ℕ) (body : List Sym) :
    let S_list := sourceValsUpTo n k body n
    let d := n - S_list.length
    let B := k * (6 * n + 9) + 6 * k + 24 * n + 30
    ∃ c ≤ n * (B + 2) + 1,
      phaseC2LoopProg.Exec (phaseC1Store n k body d)
        (phaseC2Store n k body S_list.length) c := by
  intro S_list d B
  have h0 : phaseC1Store n k body d = phaseC2Store n k body 0 := by
    funext key
    cases key <;> simp [phaseC1Store, phaseC2Store, phaseC2Table_zero, S_list, d]
  have hloop := exec_bounded_loop (fun h => (h .Scnt).isSome) phaseC2BodyProg S_list.length
    (phaseC2Store n k body) B
    (fun j hj => by
      simp [phaseC2Store, S_list, head?_replicate_isSome, Nat.sub_pos_of_lt hj])
    (by simp [phaseC2Store, S_list])
    (fun j hj => exec_phaseC2BodyProg n k body j hj)
  rcases hloop with ⟨c, hc, eloop⟩
  have hlen_le : S_list.length ≤ n := length_sourceValsUpTo_le n k body n
  have hmul_le : S_list.length * (B + 2) ≤ n * (B + 2) := Nat.mul_le_mul_right (B + 2) hlen_le
  exact ⟨c, by omega, exec_congr_left eloop h0⟩

/-! ### Stage 3: Assemble `trueBranchProg`, `mainProg`, `f_huff`, and prove `exec_mainProg` -/

lemma length_fkPart (f_val : ℕ) : ∀ a : ℕ, (fkPart f_val a).length = a * (f_val + 1)
  | 0 => by simp [fkPart]
  | a + 1 => by
    rw [fkPart_succ, List.length_append, length_fkPart f_val a, Nat.succ_mul]
    simp [encUnary]

lemma length_phaseAMidPart (k : ℕ) (body : List Sym) (q₀ : ℕ) :
    ∀ m : ℕ, (phaseAMidPart k body q₀ m).length ≤ m * (body.length + 1)
  | 0 => by simp [phaseAMidPart_zero]
  | m + 1 => by
    rw [phaseAMidPart_succ, List.length_append, Nat.succ_mul]
    have ih := length_phaseAMidPart k body q₀ m
    have hv := valAt_le_length body (q₀ * k + 1 + m)
    simp only [encUnary, List.length_append, List.length_replicate, List.length_singleton]
    omega

lemma length_phaseATable (n k : ℕ) (body : List Sym) :
    ∀ q : ℕ, (phaseATable n k body q).length ≤
      q * ((k - 1) * (body.length + 1) + 3 * body.length + 2 * n + 3)
  | 0 => by simp [phaseATable]
  | q + 1 => by
    rw [phaseATable_succ, List.length_append, Nat.succ_mul]
    have ih := length_phaseATable n k body q
    have hmid := length_phaseAMidPart k body q (k - 1)
    have hv := valAt_le_length body (q * k)
    have hex : extraVal n k body q ≤ body.length + n := by
      unfold extraVal
      split_ifs <;> omega
    simp only [phaseARow, encUnary, List.length_append, List.length_replicate, List.length_singleton]
    omega

lemma length_phaseC1Table (n k f_val : ℕ) (hf : f_val ≤ n) :
    ∀ i ≤ n, (phaseC1Table n k f_val i).length ≤ i * (k * (f_val + 1) + 4 * n + 2)
  | 0, _ => by simp [phaseC1Table_zero]
  | i + 1, hi => by
    rw [phaseC1Table_succ, List.length_append, Nat.succ_mul]
    have ih := length_phaseC1Table n k f_val hf i (by omega)
    have hfk := length_fkPart f_val k
    have hex : phaseC1ExtraVal n f_val i ≤ 2 * n := by
      unfold phaseC1ExtraVal
      split_ifs <;> omega
    simp only [phaseC1Row, encUnary, List.length_append, List.length_replicate, List.length_singleton, hfk]
    omega

lemma length_phaseC2Table (n k f_val : ℕ) (S_list : List ℕ) (d : ℕ)
    (hS : ∀ j, S_list.getD j 0 ≤ n) (hd : d ≤ n) :
    ∀ j ≤ n - d, (phaseC2Table n k f_val S_list d j).length ≤ j * (k * (f_val + 1) + 3 * n + 2)
  | 0, _ => by simp [phaseC2Table_zero]
  | j + 1, hj => by
    rw [phaseC2Table_succ, List.length_append, Nat.succ_mul]
    have ih := length_phaseC2Table n k f_val S_list d hS hd j (by omega)
    have hfk := length_fkPart f_val k
    have hsj := hS j
    have hex : phaseC2ExtraVal n (S_list.getD j 0) (d + j) ≤ 2 * n := by
      unfold phaseC2ExtraVal
      split_ifs <;> omega
    simp only [phaseC2Row, encUnary, List.length_append, List.length_replicate, List.length_singleton, hfk]
    omega


def rowAllUpTo (k : ℕ) (body : List Sym) (q a : ℕ) : Bool :=
  (List.range a).all fun j => decide (valAt body (q * k + j) = q)

lemma rowAllUpTo_zero (k : ℕ) (body : List Sym) (q : ℕ) : rowAllUpTo k body q 0 = true := rfl

lemma rowAllUpTo_succ (k : ℕ) (body : List Sym) (q a : ℕ) :
    rowAllUpTo k body q (a + 1) = (rowAllUpTo k body q a && decide (valAt body (q * k + a) = q)) := by
  simp [rowAllUpTo, List.range_succ]

def hasSinkUpTo (k : ℕ) (body : List Sym) (q : ℕ) : Bool :=
  ((List.range q).filter (isSinkVal k body)).isEmpty.not

lemma hasSinkUpTo_zero (k : ℕ) (body : List Sym) : hasSinkUpTo k body 0 = false := rfl

lemma hasSinkUpTo_succ (k : ℕ) (body : List Sym) (q : ℕ) :
    hasSinkUpTo k body (q + 1) = (hasSinkUpTo k body q || isSinkVal k body q) := by
  unfold hasSinkUpTo
  simp only [List.range_succ, List.filter_append, List.filter_singleton]
  cases h : (List.range q).filter (isSinkVal k body) <;>
    cases h' : isSinkVal k body q <;> simp [h, h']

lemma sinkValUpTo_zero (k : ℕ) (body : List Sym) : sinkValUpTo k body 0 = 0 := rfl

lemma sinkValUpTo_succ (k : ℕ) (body : List Sym) (q : ℕ) :
    sinkValUpTo k body (q + 1) =
      if hasSinkUpTo k body q = false ∧ isSinkVal k body q = true then q else sinkValUpTo k body q := by
  unfold sinkValUpTo hasSinkUpTo
  simp only [List.range_succ, List.filter_append, List.filter_singleton]
  cases h : (List.range q).filter (isSinkVal k body) <;>
    cases h' : isSinkVal k body q <;> simp [h, h']

def sinkInnerBodyProg : Prog :=
  .seq (popProg .Krem)
    (.seq (readUnaryProg .W .V0)
      (.seq (branchEqVQ (popProg .sc)
          (.seq (clearProg .Found) (pushProg .Found (some true))))
        (clearProg .V0)))

def sinkInnerLoopProg : Prog :=
  .loop (fun h => (h .Krem).isSome) sinkInnerBodyProg

def sinkStore (n k : ℕ) (body : List Sym) (q : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .Nrem => List.replicate (n - q) (some true)
  | .Q => List.replicate q (some true)
  | .W => wordAt body (q * k)
  | .F => List.replicate (sinkValUpTo k body q) (some true)
  | .D => if hasSinkUpTo k body q then [some true] else []
  | _ => []

def sinkInnerStore (n k : ℕ) (body : List Sym) (q a : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .Nrem => List.replicate (n - (q + 1)) (some true)
  | .Krem => List.replicate (k - a) (some true)
  | .Q => List.replicate q (some true)
  | .W => wordAt body (q * k + a)
  | .F => List.replicate (sinkValUpTo k body q) (some true)
  | .D => if hasSinkUpTo k body q then [some true] else []
  | .Found => if rowAllUpTo k body q a then [] else [some true]
  | _ => []

lemma exec_sinkInnerLoopProg (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ k * (15 * body.length + 12 * n + 31) + 1,
      sinkInnerLoopProg.Exec (sinkInnerStore n k body q 0)
        (sinkInnerStore n k body q k) c := by
  refine exec_bounded_loop (fun h => (h .Krem).isSome) sinkInnerBodyProg k
    (sinkInnerStore n k body q) (15 * body.length + 12 * n + 29) ?_ ?_ ?_
  · intro idx hidx
    simp [sinkInnerStore, head?_replicate_isSome, Nat.sub_pos_of_lt hidx]
  · simp [sinkInnerStore]
  · intro idx _
    set s0 := sinkInnerStore n k body q idx
    have hp1 := (stack_basic_macros SKey.Krem s0).2.1
    set s1 := Function.update s0 .Krem (s0 .Krem).tail
    have e1 : ∃ c ≤ 1, (popProg .Krem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
    have e2 := exec_readUnaryProg_wordAt .W .V0 (by decide) s1 body (q * k + idx)
      (by simp [s1, s0, sinkInnerStore]) (by simp [s1, s0, sinkInnerStore])
    set s2 := Function.update (Function.update s1 .W (wordAt body (q * k + idx + 1)))
      .V0 (List.replicate (valAt body (q * k + idx)) (some true))
    set s3_target := Function.update s2 .Found
      (if rowAllUpTo k body q (idx + 1) then [] else [some true])
    have hv_le : valAt body (q * k + idx) ≤ body.length := valAt_le_length body (q * k + idx)
    have e3 : ∃ c ≤ 9 * body.length + 12 * n + 21,
        (branchEqVQ (popProg .sc) (.seq (clearProg .Found) (pushProg .Found (some true)))).Exec
          s2 s3_target c := by
      by_cases hvq : valAt body (q * k + idx) ≠ q
      · have hc_f := (stack_basic_macros SKey.Found s2).2.2
        set sf1 := Function.update s2 .Found []
        have ef1 : ∃ c ≤ 4, (clearProg .Found).Exec s2 sf1 c := by
          refine ⟨3 * (s2 .Found).length + 1, ?_, hc_f⟩
          simp [s2, s1, s0, sinkInnerStore]
          split_ifs <;> simp
        have hp_f := (stack_basic_macros SKey.Found sf1).1 (some true)
        have ef2 : ∃ c ≤ 1, (pushProg .Found (some true)).Exec sf1 s3_target c := by
          refine ⟨1, le_rfl, exec_congr hp_f ?_⟩
          funext j
          cases j <;> simp [sf1, s3_target, s2, rowAllUpTo_succ, hvq]
        have e_br := exec_branchEqVQ_false
          (popProg .sc) (.seq (clearProg .Found) (pushProg .Found (some true)))
          s2 s3_target (valAt body (q * k + idx)) q (4 + 1 + 1)
          (by simp [s2]) (by simp [s2, s1, s0, sinkInnerStore])
          (by simp [s2, s1, s0, sinkInnerStore]) (by simp [s2, s1, s0, sinkInnerStore])
          (by simp [s2, s1, s0, sinkInnerStore]) hvq (exec_seq_le ef1 ef2)
        exact exec_le_of_le e_br (by omega)
      · have hvq : valAt body (q * k + idx) = q := by simpa using hvq
        have hpop := (stack_basic_macros SKey.sc s2).2.1
        have ef : ∃ c ≤ 1, (popProg .sc).Exec s2 s3_target c := by
          refine ⟨1, le_rfl, exec_congr hpop ?_⟩
          funext j
          cases j <;> simp [s3_target, s2, s1, s0, sinkInnerStore, rowAllUpTo_succ, hvq]
        have e_br := exec_branchEqVQ_true
          (popProg .sc) (.seq (clearProg .Found) (pushProg .Found (some true)))
          s2 s3_target (valAt body (q * k + idx)) q 1
          (by simp [s2]) (by simp [s2, s1, s0, sinkInnerStore])
          (by simp [s2, s1, s0, sinkInnerStore]) (by simp [s2, s1, s0, sinkInnerStore])
          (by simp [s2, s1, s0, sinkInnerStore]) hvq ef
        exact exec_le_of_le e_br (by omega)
    have hc4 := (stack_basic_macros SKey.V0 s3_target).2.2
    have e4 : ∃ c ≤ 3 * body.length + 1,
        (clearProg .V0).Exec s3_target (sinkInnerStore n k body q (idx + 1)) c := by
      refine ⟨3 * (s3_target .V0).length + 1, ?_, exec_congr hc4 ?_⟩
      · simp [s3_target, s2]
        omega
      · funext j
        cases j <;> simp [s3_target, s2, s1, s0, sinkInnerStore, Nat.sub_sub, Nat.add_assoc]
    have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))
    exact exec_le_of_le e_all (by omega)


lemma rowAllUpTo_full (k : ℕ) (body : List Sym) (q : ℕ) :
    rowAllUpTo k body q k = isSinkVal k body q := rfl

def sinkRecordProg : Prog :=
  .seq (clearProg .F) (.seq (copyProg .Q .F .sc) (pushProg .D (some true)))

def sinkTest (h : SKey → Option Sym) : Bool := (h .Found).isNone && (h .D).isNone

def sinkBodyProg : Prog :=
  .seq (popProg .Nrem)
    (.seq (copyProg .K .Krem .sc)
      (.seq sinkInnerLoopProg
        (.seq (.branch sinkTest sinkRecordProg (popProg .sc))
          (.seq (clearProg .Found) (pushProg .Q (some true))))))

def sinkLoopProg : Prog := .loop (fun h => (h .Nrem).isSome) sinkBodyProg

lemma exec_sinkBodyProg (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ k * (15 * body.length + 12 * n + 31) + 9 * n + 6 * k + 30,
      sinkBodyProg.Exec (sinkStore n k body q) (sinkStore n k body (q + 1)) c := by
  set s0 := sinkStore n k body q
  set s1 := Function.update s0 .Nrem (s0 .Nrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Nrem).Exec s0 s1 c :=
    ⟨1, le_rfl, (stack_basic_macros SKey.Nrem s0).2.1⟩
  have ec2 := stack_copy SKey.K SKey.Krem SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, s0, sinkStore])
  have e2 : ∃ c ≤ 6 * k + 3,
      (copyProg .K .Krem .sc).Exec s1 (sinkInnerStore n k body q 0) c := by
    refine ⟨6 * (s1 .K).length + 3, by simp [s1, s0, sinkStore], exec_congr ec2 ?_⟩
    funext j
    cases j <;> simp [s1, s0, sinkStore, sinkInnerStore, rowAllUpTo_zero, Nat.sub_sub]
  have e3 := exec_sinkInnerLoopProg n k body q hq
  set s3 := sinkInnerStore n k body q k
  set s4 := Function.update (Function.update (sinkStore n k body (q + 1)) .Q
    (List.replicate q (some true))) .Found (s3 .Found)
  have hf : sinkValUpTo k body q ≤ n := (sinkValUpTo_le k body q).trans (Nat.le_of_lt hq)
  have hi : q * k + k = (q + 1) * k := by ring
  have e4 : ∃ c ≤ 9 * n + 8,
      (StackProg.branch sinkTest sinkRecordProg (popProg .sc)).Exec s3 s4 c := by
    by_cases hs : hasSinkUpTo k body q = false ∧ isSinkVal k body q = true
    · have htest : sinkTest (fun j => (s3 j).head?) = true := by
        simp [sinkTest, s3, sinkInnerStore, rowAllUpTo_full, hs.1, hs.2]
      set st1 := Function.update s3 .F []
      have et1 : ∃ c ≤ 3 * n + 1, (clearProg .F).Exec s3 st1 c := by
        refine ⟨3 * (s3 .F).length + 1, ?_, (stack_basic_macros SKey.F s3).2.2⟩
        simp only [s3, sinkInnerStore, List.length_replicate]
        omega
      set st2 := Function.update st1 .F (st1 .Q ++ st1 .F)
      have et2 : ∃ c ≤ 6 * n + 3, (copyProg .Q .F .sc).Exec st1 st2 c := by
        refine ⟨6 * (st1 .Q).length + 3, ?_, stack_copy _ _ _ (by decide) (by decide) (by decide) st1 ?_⟩
        · simp [st1, s3, sinkInnerStore]; omega
        · simp [st1, s3, sinkInnerStore]
      have et3 : ∃ c ≤ 1, (pushProg .D (some true)).Exec st2 s4 c := by
        refine ⟨1, le_rfl, exec_congr ((stack_basic_macros SKey.D st2).1 (some true)) ?_⟩
        funext j
        cases j <;> simp [st2, st1, s4, s3, sinkInnerStore, sinkStore,
          sinkValUpTo_succ, hasSinkUpTo_succ, hs.1, hs.2, hi]
      exact exec_le_of_le (exec_branch_true_le sinkTest sinkRecordProg (popProg .sc) htest
        (exec_seq_le et1 (exec_seq_le et2 et3))) (by omega)
    · have htest : sinkTest (fun j => (s3 j).head?) = false := by
        by_cases hh : hasSinkUpTo k body q = true
        · simp [sinkTest, s3, sinkInnerStore, rowAllUpTo_full, hh]
        · have hh0 : hasSinkUpTo k body q = false := by simpa using hh
          have hr : isSinkVal k body q ≠ true := fun hr => hs ⟨hh0, hr⟩
          simp [sinkTest, s3, sinkInnerStore, rowAllUpTo_full, hh0, hr]
      have ef : ∃ c ≤ 1, (popProg .sc).Exec s3 s4 c := by
        refine ⟨1, le_rfl, exec_congr (stack_basic_macros SKey.sc s3).2.1 ?_⟩
        funext j
        cases j <;> simp [s4, s3, sinkInnerStore, sinkStore, sinkValUpTo_succ, hs, hi,
          hasSinkUpTo_succ]
        by_cases hh : hasSinkUpTo k body q = true
        · simp [hh]
        · have hh0 : hasSinkUpTo k body q = false := by simpa using hh
          have hr : isSinkVal k body q ≠ true := fun hr => hs ⟨hh0, hr⟩
          simp [hh0, hr]
      exact exec_le_of_le (exec_branch_false_le sinkTest sinkRecordProg (popProg .sc) htest ef) (by omega)
  set s5 := Function.update s4 .Found []
  have e5 : ∃ c ≤ 4, (clearProg .Found).Exec s4 s5 c := by
    refine ⟨3 * (s4 .Found).length + 1, ?_, (stack_basic_macros SKey.Found s4).2.2⟩
    simp [s4, s3, sinkInnerStore]
    split_ifs <;> simp
  have e6 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec s5 (sinkStore n k body (q + 1)) c := by
    refine ⟨1, le_rfl, exec_congr ((stack_basic_macros SKey.Q s5).1 (some true)) ?_⟩
    funext j
    cases j <;> simp [s5, s4, sinkStore, List.replicate_succ]
  exact exec_le_of_le
    (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 (exec_seq_le e5 e6))))) (by omega)

lemma exec_sinkLoopProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ n * (k * (15 * body.length + 12 * n + 31) + 9 * n + 6 * k + 32) + 1,
      sinkLoopProg.Exec (sinkStore n k body 0) (sinkStore n k body n) c := by
  refine exec_bounded_loop _ _ n (sinkStore n k body) _ ?_ ?_ ?_
  · intro q hq
    simp [sinkStore, head?_replicate_isSome, Nat.sub_pos_of_lt hq]
  · simp [sinkStore]
  · intro q hq
    exact exec_sinkBodyProg n k body q hq

def sinkInitProg : Prog :=
  .seq (clearProg .Nrem) (.seq (copyProg .N .Nrem .sc) (copyProg .ki .W .sc))

def sinkFinishProg : Prog :=
  .seq (clearProg .W) (.seq (clearProg .Q) (.seq (clearProg .D)
    (.seq (copyProg .N .Nrem .sc) (popProg .Nrem))))

def findSinkProg : Prog := .seq sinkInitProg (.seq sinkLoopProg sinkFinishProg)

lemma exec_sinkInitProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 9 * n + 6 * body.length + 9,
      sinkInitProg.Exec (storeAfterHeaderRead n k body) (sinkStore n k body 0) c := by
  set s0 := storeAfterHeaderRead n k body
  set s1 := Function.update s0 .Nrem []
  have e1 : ∃ c ≤ 3 * n + 1, (clearProg .Nrem).Exec s0 s1 c := by
    refine ⟨3 * (s0 .Nrem).length + 1, ?_, (stack_basic_macros SKey.Nrem s0).2.2⟩
    simp [s0, storeAfterHeaderRead]
  set s2 := Function.update s1 .Nrem (s1 .N ++ s1 .Nrem)
  have e2 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .N).length + 3, by simp [s1, s0, storeAfterHeaderRead],
      stack_copy _ _ _ (by decide) (by decide) (by decide) s1 ?_⟩
    simp [s1, s0, storeAfterHeaderRead]
  have e3 : ∃ c ≤ 6 * body.length + 3, (copyProg .ki .W .sc).Exec s2 (sinkStore n k body 0) c := by
    refine ⟨6 * (s2 .ki).length + 3, by simp [s2, s1, s0, storeAfterHeaderRead],
      exec_congr (stack_copy _ _ _ (by decide) (by decide) (by decide) s2 ?_) ?_⟩
    · simp [s2, s1, s0, storeAfterHeaderRead]
    · funext j
      cases j <;> simp [s2, s1, s0, storeAfterHeaderRead, sinkStore, sinkValUpTo_zero, hasSinkUpTo_zero, wordAt]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

lemma exec_sinkFinishProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 9 * n + 3 * body.length + 14,
      sinkFinishProg.Exec (sinkStore n k body n) (storeAfterSink n k body) c := by
  set s0 := sinkStore n k body n
  set s1 := Function.update s0 .W []
  have e1 : ∃ c ≤ 3 * body.length + 1, (clearProg .W).Exec s0 s1 c := by
    refine ⟨3 * (s0 .W).length + 1, ?_, (stack_basic_macros SKey.W s0).2.2⟩
    have h := length_wordAt_le body (n * k)
    simp only [s0, sinkStore]
    omega
  set s2 := Function.update s1 .Q []
  have e2 : ∃ c ≤ 3 * n + 1, (clearProg .Q).Exec s1 s2 c := by
    exact ⟨3 * (s1 .Q).length + 1, by simp [s1, s0, sinkStore], (stack_basic_macros SKey.Q s1).2.2⟩
  set s3 := Function.update s2 .D []
  have e3 : ∃ c ≤ 4, (clearProg .D).Exec s2 s3 c := by
    refine ⟨3 * (s2 .D).length + 1, ?_, (stack_basic_macros SKey.D s2).2.2⟩
    simp [s2, s1, s0, sinkStore]
    split_ifs <;> simp
  set s4 := Function.update s3 .Nrem (s3 .N ++ s3 .Nrem)
  have e4 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s3 s4 c := by
    refine ⟨6 * (s3 .N).length + 3, by simp [s3, s2, s1, s0, sinkStore],
      stack_copy _ _ _ (by decide) (by decide) (by decide) s3 ?_⟩
    simp [s3, s2, s1, s0, sinkStore]
  have e5 : ∃ c ≤ 1, (popProg .Nrem).Exec s4 (storeAfterSink n k body) c := by
    refine ⟨1, le_rfl, exec_congr (stack_basic_macros SKey.Nrem s4).2.1 ?_⟩
    funext j
    cases j <;> simp [s4, s3, s2, s1, s0, sinkStore, storeAfterSink, storeAfterHeaderRead]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 (exec_seq_le e4 e5)))) (by omega)

lemma exec_findSinkProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ n * (k * (15 * body.length + 12 * n + 31) + 9 * n + 6 * k + 32) +
        18 * n + 9 * body.length + 26,
      findSinkProg.Exec (storeAfterHeaderRead n k body) (storeAfterSink n k body) c := by
  exact exec_le_of_le (exec_seq_le (exec_sinkInitProg n k body)
    (exec_seq_le (exec_sinkLoopProg n k body) (exec_sinkFinishProg n k body))) (by omega)

def emitFK2TimesProg : Prog := .seq (copyProg .K2 .Krem .sc) emitFKLoopProg

lemma exec_emitFK2TimesProg (s : Store) (n k f_val : ℕ)
    (hK : s .K2 = List.replicate k (some true))
    (hKrem : s .Krem = [])
    (hF : s .F = List.replicate f_val (some true))
    (hsc : s .sc = [])
    (hf_le : f_val ≤ n) :
    ∃ c ≤ k * (6 * n + 9) + 6 * k + 5,
      emitFK2TimesProg.Exec s
        (Function.update s .outRev ((fkPart f_val k).reverse ++ s .outRev)) c := by
  have hc1 := stack_copy SKey.K2 SKey.Krem SKey.sc (by decide) (by decide) (by decide) s hsc
  have e1 : ∃ c ≤ 6 * k + 3, (copyProg .K2 .Krem .sc).Exec s (sEmitFK s k f_val 0) c := by
    refine ⟨6 * (s .K2).length + 3, by simp [hK], exec_congr hc1 ?_⟩
    funext j
    cases j <;> simp [sEmitFK, fkPart_zero, hK, hKrem]
  have hloop := exec_bounded_loop (fun h => (h .Krem).isSome) emitFKBodyProg k
    (sEmitFK s k f_val) (6 * n + 7)
    (fun a ha => by
      show (sEmitFK s k f_val a .Krem).head?.isSome = true
      simp [sEmitFK, head?_replicate_isSome, Nat.sub_pos_of_lt ha])
    (by
      show (sEmitFK s k f_val k .Krem).head?.isSome = false
      simp [sEmitFK])
    (fun a _ => by
      set s0 := sEmitFK s k f_val a
      have hp1 := (stack_basic_macros SKey.Krem s0).2.1
      set s1 := Function.update s0 .Krem (s0 .Krem).tail
      have ep1 : ∃ c ≤ 1, (popProg .Krem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
      have ep2 := exec_emitUnaryTo .F .outRev (by decide) (by decide) (by decide) s1 f_val
        (by simp [s1, s0, sEmitFK, hF]) (by simp [s1, s0, sEmitFK, hsc])
      have ep2' : ∃ c ≤ 6 * f_val + 5,
          (emitUnaryTo .F .outRev).Exec s1 (sEmitFK s k f_val (a + 1)) c := by
        rcases ep2 with ⟨c2, hc2, ec2⟩
        refine ⟨c2, hc2, exec_congr ec2 ?_⟩
        funext j
        cases j <;> simp [s1, s0, sEmitFK, fkPart_succ, List.reverse_append, Nat.sub_sub]
      exact exec_le_of_le (exec_seq_le ep1 ep2') (by omega))
  rcases hloop with ⟨c2, hc2, eloop⟩
  have e2 : ∃ c ≤ k * (6 * n + 9) + 1,
      emitFKLoopProg.Exec (sEmitFK s k f_val 0)
        (Function.update s .outRev ((fkPart f_val k).reverse ++ s .outRev)) c := by
    refine ⟨c2, hc2, exec_congr eloop ?_⟩
    funext j
    cases j <;> simp [sEmitFK, hKrem]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)



def identityTable (k q : ℕ) : List Sym :=
  (List.range q).flatMap fun i => fkPart i (k + 2)

lemma identityTable_succ (k q : ℕ) :
    identityTable k (q + 1) = identityTable k q ++ fkPart q (k + 2) := by
  simp [identityTable, List.range_succ]

def identityHeaderRev (n k : ℕ) : List Sym :=
  (encUnary (k + 2)).reverse ++ (encUnary n).reverse

def identityStore (n k : ℕ) (body : List Sym) (q : ℕ) : Store := fun j =>
  match j with
  | .ki => body
  | .N => List.replicate n (some true)
  | .K => List.replicate k (some true)
  | .K2 => List.replicate (k + 2) (some true)
  | .Nrem => List.replicate (n - q) (some true)
  | .F => List.replicate q (some true)
  | .outRev => (identityTable k q).reverse ++ identityHeaderRev n k
  | _ => []

def identityInitProg : Prog :=
  .seq (clearProg .Nrem) (.seq (copyProg .N .Nrem .sc)
    (.seq (emitUnaryTo .N .outRev) (emitUnaryTo .K2 .outRev)))

def identityBodyProg : Prog :=
  .seq (popProg .Nrem) (.seq emitFK2TimesProg (pushProg .F (some true)))

def identityLoopProg : Prog := .loop (fun h => (h .Nrem).isSome) identityBodyProg

def falseBranchProg : Prog := .seq identityInitProg identityLoopProg

lemma exec_identityInitProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ 15 * n + 6 * k + 29,
      identityInitProg.Exec (storeAfterHeaderRead n k body) (identityStore n k body 0) c := by
  set s0 := storeAfterHeaderRead n k body
  set s1 := Function.update s0 .Nrem []
  have e1 : ∃ c ≤ 3 * n + 1, (clearProg .Nrem).Exec s0 s1 c := by
    refine ⟨3 * (s0 .Nrem).length + 1, ?_, (stack_basic_macros SKey.Nrem s0).2.2⟩
    simp [s0, storeAfterHeaderRead]
  set s2 := Function.update s1 .Nrem (s1 .N ++ s1 .Nrem)
  have e2 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s1 s2 c := by
    refine ⟨6 * (s1 .N).length + 3, by simp [s1, s0, storeAfterHeaderRead],
      stack_copy _ _ _ (by decide) (by decide) (by decide) s1 ?_⟩
    simp [s1, s0, storeAfterHeaderRead]
  have e3 := exec_emitUnaryTo .N .outRev (by decide) (by decide) (by decide) s2 n
    (by simp [s2, s1, s0, storeAfterHeaderRead]) (by simp [s2, s1, s0, storeAfterHeaderRead])
  set s3 := Function.update s2 .outRev ((encUnary n).reverse ++ s2 .outRev)
  have ec4 := exec_emitUnaryTo .K2 .outRev (by decide) (by decide) (by decide) s3 (k + 2)
    (by simp [s3, s2, s1, s0, storeAfterHeaderRead]) (by simp [s3, s2, s1, s0, storeAfterHeaderRead])
  have e4 : ∃ c ≤ 6 * (k + 2) + 5,
      (emitUnaryTo .K2 .outRev).Exec s3 (identityStore n k body 0) c := by
    rcases ec4 with ⟨c, hc, he⟩
    refine ⟨c, hc, exec_congr he ?_⟩
    funext j
    cases j <;> simp [s3, s2, s1, s0, storeAfterHeaderRead, identityStore,
      identityTable, identityHeaderRev]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))) (by omega)

lemma exec_identityBodyProg (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ (k + 2) * (6 * n + 9) + 6 * k + 21,
      identityBodyProg.Exec (identityStore n k body q) (identityStore n k body (q + 1)) c := by
  set s0 := identityStore n k body q
  set s1 := Function.update s0 .Nrem (s0 .Nrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Nrem).Exec s0 s1 c :=
    ⟨1, le_rfl, (stack_basic_macros SKey.Nrem s0).2.1⟩
  have e2 := exec_emitFK2TimesProg s1 n (k + 2) q
    (by simp [s1, s0, identityStore]) (by simp [s1, s0, identityStore])
    (by simp [s1, s0, identityStore]) (by simp [s1, s0, identityStore]) (by omega)
  set s2 := Function.update s1 .outRev ((fkPart q (k + 2)).reverse ++ s1 .outRev)
  have e3 : ∃ c ≤ 1, (pushProg .F (some true)).Exec s2 (identityStore n k body (q + 1)) c := by
    refine ⟨1, le_rfl, exec_congr ((stack_basic_macros SKey.F s2).1 (some true)) ?_⟩
    funext j
    cases j <;> simp [s2, s1, s0, identityStore, identityTable_succ,
      List.reverse_append, Nat.sub_sub, List.replicate_succ, List.append_assoc]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

lemma exec_identityLoopProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ n * ((k + 2) * (6 * n + 9) + 6 * k + 23) + 1,
      identityLoopProg.Exec (identityStore n k body 0) (identityStore n k body n) c := by
  refine exec_bounded_loop _ _ n (identityStore n k body) _ ?_ ?_ ?_
  · intro q hq
    simp [identityStore, head?_replicate_isSome, Nat.sub_pos_of_lt hq]
  · simp [identityStore]
  · intro q hq
    exact exec_identityBodyProg n k body q hq

lemma exec_falseBranchProg (n k : ℕ) (body : List Sym) :
    ∃ c ≤ n * ((k + 2) * (6 * n + 9) + 6 * k + 23) + 15 * n + 6 * k + 31,
      falseBranchProg.Exec (storeAfterHeaderRead n k body) (identityStore n k body n) c := by
  exact exec_le_of_le (exec_seq_le (exec_identityInitProg n k body) (exec_identityLoopProg n k body)) (by omega)

lemma identityStore_outRev (n k : ℕ) (body : List Sym) :
    identityStore n k body n .outRev = falseOutRev n k := by
  simp [identityStore, falseOutRev, identityTable, identityHeaderRev, fkPart,
    List.reverse_append, List.append_assoc]

lemma length_identityTable (n k : ℕ) :
    ∀ q ≤ n, (identityTable k q).length ≤ q * ((k + 2) * (n + 1))
  | 0, _ => by simp [identityTable]
  | q + 1, hq => by
    rw [identityTable_succ, List.length_append, length_fkPart]
    have h := length_identityTable n k q (by omega)
    have hm := Nat.mul_le_mul_left (k + 2) (show q + 1 ≤ n + 1 by omega)
    nlinarith

lemma length_falseOutRev (n k : ℕ) :
    (falseOutRev n k).length ≤ n * ((k + 2) * (n + 1)) + n + k + 4 := by
  have h := length_identityTable n k n le_rfl
  have he : (falseOutRev n k).length = (identityTable k n).length + n + k + 4 := by
    simp [falseOutRev, identityTable, fkPart, encUnary, add_assoc, add_comm, add_left_comm]
  omega

def trueEmitProg : Prog :=
  .seq trueInitProg
    (.seq phaseALoopProg
      (.seq phaseAToBProg
        (.seq phaseBLoopProg
          (.seq phaseBToCProg
            (.seq phaseC1LoopProg phaseC2LoopProg)))))

def trueBranchProg : Prog := .seq findSinkProg trueEmitProg

def isTrueBranchTest (h : SKey → Option Sym) : Bool :=
  (h .Nrem).isSome && (h .K).isSome

def mainProg : Prog :=
  .seq initHeaderReadProg
    (.seq (.branch isTrueBranchTest trueBranchProg falseBranchProg)
      (transferProg .outRev (fun j => decide (j = .ko))))

set_option maxHeartbeats 800000 in
lemma exec_trueEmitProg_le_M4 (n k : ℕ) (hk : 1 ≤ k) (body : List Sym) (M : ℕ)
    (h1M : 1 ≤ M) (hn : n ≤ M) (hkM : k ≤ M) (hb : body.length ≤ M) :
    let S_list := sourceValsUpTo n k body n
    ∃ c ≤ 640 * ((M * M) * (M * M)),
      trueEmitProg.Exec (storeAfterSink n k body)
        (phaseC2Store n k body S_list.length) c := by
  intro S_list
  set M2 := M * M
  set M3 := M * M2
  set M4 := M2 * M2
  have hM_M2 : M ≤ M2 := by simpa [M2] using Nat.le_mul_of_pos_left M h1M
  have h1_M2 : 1 ≤ M2 := le_trans h1M hM_M2
  have hM2_M3 : M2 ≤ M3 := by simpa [M3] using Nat.le_mul_of_pos_left M2 h1M
  have hM_M3 : M ≤ M3 := le_trans hM_M2 hM2_M3
  have h1_M3 : 1 ≤ M3 := le_trans h1_M2 hM2_M3
  have hM2_M4 : M2 ≤ M4 := by simpa [M4] using Nat.le_mul_of_pos_left M2 h1_M2
  have hM3_M4 : M3 ≤ M4 := by
    have hmul2 := Nat.mul_le_mul h1M (le_refl M3)
    have heq3 : M * M3 = M4 := by dsimp [M4, M3, M2]; ring
    omega
  have hM_M4 : M ≤ M4 := le_trans hM_M2 hM2_M4
  have h1_M4 : 1 ≤ M4 := le_trans h1_M2 hM2_M4
  have hnk_M2 : n * k ≤ M2 := Nat.mul_le_mul hn hkM
  have hnn_M2 : n * n ≤ M2 := Nat.mul_le_mul hn hn
  have e1 : ∃ c ≤ 125 * M4,
      trueInitProg.Exec (storeAfterSink n k body) (phaseAStore n k body 0) c := by
    refine exec_le_of_le (exec_trueInitProg n k body) ?_
    have h6nk : 6 * n * k = 6 * (n * k) := by ring
    omega
  have e2 : ∃ c ≤ 174 * M4,
      phaseALoopProg.Exec (phaseAStore n k body 0) (phaseAStore n k body n) c := by
    refine exec_le_of_le (exec_phaseALoopProg n k hk body) ?_
    have hk1_M : k - 1 ≤ M := by omega
    have h12b : 12 * body.length + 15 ≤ 27 * M := by omega
    have h_mid : (k - 1) * (12 * body.length + 15) ≤ 27 * M2 := by
      have hmul := Nat.mul_le_mul hk1_M h12b
      have heq : M * (27 * M) = 27 * M2 := by dsimp [M2]; ring
      exact le_trans hmul (le_of_eq heq)
    have h_B : (k - 1) * (12 * body.length + 15) + 33 * body.length + 40 * n + 6 * k + 65 + 2 ≤
        173 * M2 := by omega
    have h_nB : n * ((k - 1) * (12 * body.length + 15) + 33 * body.length + 40 * n + 6 * k + 65 + 2) ≤
        173 * M3 := by
      have hmul := Nat.mul_le_mul hn h_B
      have heq : M * (173 * M2) = 173 * M3 := by dsimp [M3]; ring
      exact le_trans hmul (le_of_eq heq)
    omega
  have e3 : ∃ c ≤ 19 * M4,
      phaseAToBProg.Exec (phaseAStore n k body n) (phaseBStore n k body 0) c := by
    refine exec_le_of_le (exec_phaseAToBProg n k body) ?_
    omega
  have e4 : ∃ c ≤ 145 * M4,
      phaseBLoopProg.Exec (phaseBStore n k body 0) (phaseBStore n k body n) c := by
    refine exec_le_of_le (exec_phaseBLoopProg n k body) ?_
    have h15b : 15 * body.length + 12 * n + 31 ≤ 58 * M := by omega
    have h_nk_in : (n * k) * (15 * body.length + 12 * n + 31) ≤ 58 * M3 := by
      have hmul := Nat.mul_le_mul hnk_M2 h15b
      have heq : M2 * (58 * M) = 58 * M3 := by dsimp [M3, M2]; ring
      exact le_trans hmul (le_of_eq heq)
    have h_B : (n * k) * (15 * body.length + 12 * n + 31) + 6 * (n * k) + 9 * body.length + 27 * n + 42 + 2 ≤
        144 * M3 := by omega
    have h_nB : n * ((n * k) * (15 * body.length + 12 * n + 31) + 6 * (n * k) + 9 * body.length + 27 * n + 42 + 2) ≤
        144 * M4 := by
      have hmul := Nat.mul_le_mul hn h_B
      have heq : M * (144 * M3) = 144 * M4 := by dsimp [M4, M3, M2]; ring
      exact le_trans hmul (le_of_eq heq)
    omega
  have e5 : ∃ c ≤ 17 * M4,
      phaseBToCProg.Exec (phaseBStore n k body n) (phaseC1Store n k body 0) c := by
    refine exec_le_of_le (exec_phaseBToCProg n k body) ?_
    omega
  have h6n9 : 6 * n + 9 ≤ 15 * M := by omega
  have hk_6n9 : k * (6 * n + 9) ≤ 15 * M2 := by
    have hmul := Nat.mul_le_mul hkM h6n9
    have heq : M * (15 * M) = 15 * M2 := by dsimp [M2]; ring
    exact le_trans hmul (le_of_eq heq)
  have e6 : ∃ c ≤ 72 * M4,
      phaseC1LoopProg.Exec (phaseC1Store n k body 0)
        (phaseC1Store n k body (n - S_list.length)) c := by
    refine exec_le_of_le (exec_phaseC1LoopProg n k body) ?_
    have h_B : k * (6 * n + 9) + 6 * k + 24 * n + 24 + 2 ≤ 71 * M2 := by omega
    have h_nB : n * (k * (6 * n + 9) + 6 * k + 24 * n + 24 + 2) ≤ 71 * M3 := by
      have hmul := Nat.mul_le_mul hn h_B
      have heq : M * (71 * M2) = 71 * M3 := by dsimp [M3]; ring
      exact le_trans hmul (le_of_eq heq)
    omega
  have e7 : ∃ c ≤ 78 * M4,
      phaseC2LoopProg.Exec (phaseC1Store n k body (n - S_list.length))
        (phaseC2Store n k body S_list.length) c := by
    refine exec_le_of_le (exec_phaseC2LoopProg n k body) ?_
    have h_B : k * (6 * n + 9) + 6 * k + 24 * n + 30 + 2 ≤ 77 * M2 := by omega
    have h_nB : n * (k * (6 * n + 9) + 6 * k + 24 * n + 30 + 2) ≤ 77 * M3 := by
      have hmul := Nat.mul_le_mul hn h_B
      have heq : M * (77 * M2) = 77 * M3 := by dsimp [M3]; ring
      exact le_trans hmul (le_of_eq heq)
    omega
  have e_all := exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3
    (exec_seq_le e4 (exec_seq_le e5 (exec_seq_le e6 e7)))))
  exact exec_le_of_le e_all (by omega)



lemma exec_findSinkProg_le_M4 (n k : ℕ) (body : List Sym) (M : ℕ)
    (h1M : 1 ≤ M) (hn : n ≤ M) (hk : k ≤ M) (hb : body.length ≤ M) :
    ∃ c ≤ 160 * ((M * M) * (M * M)),
      findSinkProg.Exec (storeAfterHeaderRead n k body) (storeAfterSink n k body) c := by
  refine exec_le_of_le (exec_findSinkProg n k body) ?_
  set M2 := M * M
  set M3 := M * M2
  set M4 := M2 * M2
  have hM2 : M ≤ M2 := by dsimp [M2]; nlinarith
  have hM3 : M2 ≤ M3 := by dsimp [M3]; nlinarith
  have hM4 : M3 ≤ M4 := by dsimp [M4, M3, M2]; nlinarith
  have hp : k * (15 * body.length + 12 * n + 31) ≤ 58 * M2 := by
    have hh := Nat.mul_le_mul hk (show 15 * body.length + 12 * n + 31 ≤ 58 * M by omega)
    simpa [M2, mul_assoc, mul_comm, mul_left_comm] using hh
  have hq : k * (15 * body.length + 12 * n + 31) + 9 * n + 6 * k + 32 ≤ 105 * M2 := by omega
  have hr : n * (k * (15 * body.length + 12 * n + 31) + 9 * n + 6 * k + 32) ≤ 105 * M3 := by
    have hh := Nat.mul_le_mul hn hq
    simpa [M3, mul_assoc, mul_comm, mul_left_comm] using hh
  omega

lemma exec_trueBranchProg_le_M4 (n k : ℕ) (hk : 1 ≤ k) (body : List Sym) (M : ℕ)
    (h1M : 1 ≤ M) (hn : n ≤ M) (hkM : k ≤ M) (hb : body.length ≤ M) :
    let S_list := sourceValsUpTo n k body n
    ∃ c ≤ 802 * ((M * M) * (M * M)),
      trueBranchProg.Exec (storeAfterHeaderRead n k body)
        (phaseC2Store n k body S_list.length) c := by
  intro S_list
  have hpos : 1 ≤ (M * M) * (M * M) := by
    simpa using Nat.mul_le_mul (Nat.mul_le_mul h1M h1M) (Nat.mul_le_mul h1M h1M)
  exact exec_le_of_le (exec_seq_le (exec_findSinkProg_le_M4 n k body M h1M hn hkM hb)
    (exec_trueEmitProg_le_M4 n k hk body M h1M hn hkM hb)) (by omega)

lemma exec_falseBranchProg_le_M4 (n k : ℕ) (body : List Sym) (M : ℕ)
    (h1M : 1 ≤ M) (hn : n ≤ M) (hk : k ≤ M) :
    ∃ c ≤ 130 * ((M * M) * (M * M)),
      falseBranchProg.Exec (storeAfterHeaderRead n k body) (identityStore n k body n) c := by
  refine exec_le_of_le (exec_falseBranchProg n k body) ?_
  set M2 := M * M
  set M3 := M * M2
  set M4 := M2 * M2
  have hM2 : M ≤ M2 := by dsimp [M2]; nlinarith
  have hM3 : M2 ≤ M3 := by dsimp [M3]; nlinarith
  have hM4 : M3 ≤ M4 := by dsimp [M4, M3, M2]; nlinarith
  have hp : (k + 2) * (6 * n + 9) ≤ 45 * M2 := by
    have hh := Nat.mul_le_mul (show k + 2 ≤ 3 * M by omega)
      (show 6 * n + 9 ≤ 15 * M by omega)
    dsimp [M2]
    nlinarith
  have hq : (k + 2) * (6 * n + 9) + 6 * k + 23 ≤ 74 * M2 := by omega
  have hr : n * ((k + 2) * (6 * n + 9) + 6 * k + 23) ≤ 74 * M3 := by
    have hh := Nat.mul_le_mul hn hq
    simpa [M3, mul_assoc, mul_comm, mul_left_comm] using hh
  omega

lemma length_falseOutRev_le_M4 (n k M : ℕ) (h1M : 1 ≤ M) (hn : n ≤ M) (hk : k ≤ M) :
    (falseOutRev n k).length ≤ 12 * ((M * M) * (M * M)) := by
  have he := length_falseOutRev n k
  set M2 := M * M
  set M3 := M * M2
  set M4 := M2 * M2
  have hM2 : M ≤ M2 := by dsimp [M2]; nlinarith
  have hM3 : M2 ≤ M3 := by dsimp [M3]; nlinarith
  have hM4 : M3 ≤ M4 := by dsimp [M4, M3, M2]; nlinarith
  have hp : (k + 2) * (n + 1) ≤ 6 * M2 := by
    have hh := Nat.mul_le_mul (show k + 2 ≤ 3 * M by omega) (show n + 1 ≤ 2 * M by omega)
    dsimp [M2]
    nlinarith
  have hq : n * ((k + 2) * (n + 1)) ≤ 6 * M3 := by
    have hh := Nat.mul_le_mul hn hp
    simpa [M3, mul_assoc, mul_comm, mul_left_comm] using hh
  omega

lemma length_trueOut_le_M4 (n k : ℕ) (body : List Sym) (M : ℕ)
    (h1M : 1 ≤ M) (hn : n ≤ M) (hkM : k ≤ M) (hb : body.length ≤ M) :
    (trueOut n k body).length ≤ 35 * ((M * M) * (M * M)) := by
  set f_val := sinkValUpTo k body n
  set S_list := sourceValsUpTo n k body n
  set d := n - S_list.length
  have hf_le : f_val ≤ n := sinkValUpTo_le k body n
  have hlen_S : S_list.length ≤ n := length_sourceValsUpTo_le n k body n
  have hd_le : d ≤ n := Nat.sub_le _ _
  have hS_getD : ∀ j, S_list.getD j 0 ≤ n := getD_sourceValsUpTo_le n k body n
  have hA := length_phaseATable n k body n
  have hC1 := length_phaseC1Table n k f_val hf_le d hd_le
  have hC2 := length_phaseC2Table n k f_val S_list d hS_getD hd_le S_list.length (by omega)
  set M2 := M * M
  set M3 := M * M2
  set M4 := M2 * M2
  have hM_M2 : M ≤ M2 := by simpa [M2] using Nat.le_mul_of_pos_left M h1M
  have h1_M2 : 1 ≤ M2 := le_trans h1M hM_M2
  have hM2_M3 : M2 ≤ M3 := by simpa [M3] using Nat.le_mul_of_pos_left M2 h1M
  have hM_M3 : M ≤ M3 := le_trans hM_M2 hM2_M3
  have hM2_M4 : M2 ≤ M4 := by simpa [M4] using Nat.le_mul_of_pos_left M2 h1_M2
  have hM3_M4 : M3 ≤ M4 := by
    have hmul2 := Nat.mul_le_mul h1M (le_refl M3)
    have heq3 : M * M3 = M4 := by dsimp [M4, M3, M2]; ring
    omega
  have hM_M4 : M ≤ M4 := le_trans hM_M2 hM2_M4
  have h1_M4 : 1 ≤ M4 := le_trans h1_M2 hM2_M4
  have hk1_M : k - 1 ≤ M := by omega
  have hb1_M : body.length + 1 ≤ 2 * M := by omega
  have h_k1_b1 : (k - 1) * (body.length + 1) ≤ 2 * M2 := by
    have hmul := Nat.mul_le_mul hk1_M hb1_M
    have heq : M * (2 * M) = 2 * M2 := by dsimp [M2]; ring
    omega
  have hA_in : (k - 1) * (body.length + 1) + 3 * body.length + 2 * n + 3 ≤ 10 * M2 := by omega
  have hA_M3 : (phaseATable n k body n).length ≤ 10 * M3 := by
    have hmul := Nat.mul_le_mul hn hA_in
    have heq : M * (10 * M2) = 10 * M3 := by dsimp [M3]; ring
    omega
  have hf1_M : f_val + 1 ≤ 2 * M := by omega
  have h_k_f1 : k * (f_val + 1) ≤ 2 * M2 := by
    have hmul := Nat.mul_le_mul hkM hf1_M
    have heq : M * (2 * M) = 2 * M2 := by dsimp [M2]; ring
    omega
  have hC1_in : k * (f_val + 1) + 4 * n + 2 ≤ 8 * M2 := by omega
  have hC1_M3 : (phaseC1Table n k f_val d).length ≤ 8 * M3 := by
    have hd_M : d ≤ M := le_trans hd_le hn
    have hmul := Nat.mul_le_mul hd_M hC1_in
    have heq : M * (8 * M2) = 8 * M3 := by dsimp [M3]; ring
    omega
  have hC2_in : k * (f_val + 1) + 3 * n + 2 ≤ 7 * M2 := by omega
  have hC2_M3 : (phaseC2Table n k f_val S_list d S_list.length).length ≤ 7 * M3 := by
    have hS_M : S_list.length ≤ M := le_trans hlen_S hn
    have hmul := Nat.mul_le_mul hS_M hC2_in
    have heq : M * (7 * M2) = 7 * M3 := by dsimp [M3]; ring
    omega
  have h_out : (trueOut n k body).length =
      (2 * n + 1) + (k + 2 + 1) + (phaseATable n k body n).length +
        (phaseC1Table n k f_val d).length +
        (phaseC2Table n k f_val S_list d S_list.length).length := by
    have h_def : trueOut n k body =
        (headerRev n k).reverse ++
          phaseATable n k body n ++
          phaseC1Table n k f_val d ++
          phaseC2Table n k f_val S_list d S_list.length := rfl
    rw [h_def]
    simp only [headerRev, encUnary, List.length_append, List.length_reverse,
      List.length_replicate, List.length_singleton]
    omega
  omega



lemma exec_mainProg (w : List Sym) :
    ∃ s c, c ≤ 1000 * (w.length + 1) ^ 4 ∧
      mainProg.Exec (fun j => if j = .ki then w else []) s c ∧
      s .ko = f_huff w := by
  set L := w.length
  set M := L + 1
  set M2 := M * M
  set M4 := M2 * M2
  have hpow4 : M ^ 4 = M4 := by dsimp [M4, M2]; ring
  set n := valAt w 0
  set k := valAt w 1
  set body := wordAt w 2
  have h1M : 1 ≤ M := by omega
  have hnL : n ≤ L := valAt_le_length w 0
  have hkL : k ≤ L := valAt_le_length w 1
  have hbL : body.length ≤ L := length_wordAt_le w 2
  have hnM : n ≤ M := by omega
  have hkM : k ≤ M := by omega
  have hbM : body.length ≤ M := by omega
  have hM_M2 : M ≤ M2 := by simpa [M2] using Nat.le_mul_of_pos_left M h1M
  have h1_M2 : 1 ≤ M2 := le_trans h1M hM_M2
  have hM2_M4 : M2 ≤ M4 := by simpa [M4] using Nat.le_mul_of_pos_left M2 h1_M2
  have hM_M4 : M ≤ M4 := le_trans hM_M2 hM2_M4
  have h1_M4 : 1 ≤ M4 := le_trans h1_M2 hM2_M4
  have e1 : ∃ c ≤ 43 * M4,
      initHeaderReadProg.Exec (fun j => if j = .ki then w else [])
        (storeAfterHeaderRead n k body) c := by
    refine exec_le_of_le (exec_initHeaderReadProg w) ?_
    omega
  by_cases hcond : 2 ≤ n ∧ 1 ≤ k
  · have htest : isTrueBranchTest (fun j => (storeAfterHeaderRead n k body j).head?) = true := by
      unfold isTrueBranchTest
      simp [storeAfterHeaderRead, head?_replicate_isSome,
        show 0 < n - 1 by omega, show 0 < k by omega]
    have e_true : ∃ c ≤ 802 * M4,
        trueBranchProg.Exec (storeAfterHeaderRead n k body)
          (phaseC2Store n k body (sourceValsUpTo n k body n).length) c :=
      exec_trueBranchProg_le_M4 n k hcond.2 body M h1M hnM hkM hbM
    have e2 := exec_branch_true_le isTrueBranchTest trueBranchProg falseBranchProg htest e_true
    set s2 := phaseC2Store n k body (sourceValsUpTo n k body n).length
    have ht3 := stack_transfer SKey.outRev (fun j => decide (j = .ko)) s2
    set s3 := transferStore .outRev (fun j => decide (j = .ko)) s2
    have hout_eq : s2 .outRev = (trueOut n k body).reverse := by
      simp [s2, phaseC2Store, trueOut, List.reverse_append, List.append_assoc]
    have hout_len : (s2 .outRev).length ≤ 35 * M4 := by
      rw [hout_eq, List.length_reverse]
      exact length_trueOut_le_M4 n k body M h1M hnM hkM hbM
    have e3 : ∃ c ≤ 106 * M4,
        (transferProg .outRev (fun j => decide (j = .ko))).Exec s2 s3 c :=
      ⟨3 * (s2 .outRev).length + 1, by omega, ht3⟩
    have e_all := exec_seq_le e1 (exec_seq_le e2 e3)
    rcases e_all with ⟨c, hc, ec⟩
    refine ⟨s3, c, ?_, ec, ?_⟩
    · rw [hpow4]
      omega
    · have hko : s2 .ko = [] := rfl
      simp [s3, transferStore, hko, hout_eq, f_huff, n, k, body, hcond]
  · have htest : isTrueBranchTest (fun j => (storeAfterHeaderRead n k body j).head?) = false := by
      unfold isTrueBranchTest
      by_cases hn2 : 2 ≤ n
      · have hk0 : k = 0 := by omega
        simp [storeAfterHeaderRead, hk0]
      · have hn1 : n - 1 = 0 := by omega
        simp [storeAfterHeaderRead, hn1]
    have e_false : ∃ c ≤ 130 * M4,
        falseBranchProg.Exec (storeAfterHeaderRead n k body)
          (identityStore n k body n) c := by
      exact exec_falseBranchProg_le_M4 n k body M h1M hnM hkM
    have e2 := exec_branch_false_le isTrueBranchTest trueBranchProg falseBranchProg htest e_false
    set s2 := identityStore n k body n
    have ht3 := stack_transfer SKey.outRev (fun j => decide (j = .ko)) s2
    set s3 := transferStore .outRev (fun j => decide (j = .ko)) s2
    have hout_len : (s2 .outRev).length ≤ 12 * M4 := by
      rw [show s2 .outRev = falseOutRev n k from identityStore_outRev n k body]
      exact length_falseOutRev_le_M4 n k M h1M hnM hkM
    have e3 : ∃ c ≤ 37 * M4,
        (transferProg .outRev (fun j => decide (j = .ko))).Exec s2 s3 c :=
      ⟨3 * (s2 .outRev).length + 1, by omega, ht3⟩
    have e_all := exec_seq_le e1 (exec_seq_le e2 e3)
    rcases e_all with ⟨c, hc, ec⟩
    refine ⟨s3, c, ?_, ec, ?_⟩
    · rw [hpow4]
      omega
    · simp [s3, transferStore, s2, identityStore_outRev, identityStore, f_huff, n, k, body, hcond,
        falseOutRev, identityTable, identityHeaderRev, fkPart, List.reverse_append, List.append_assoc]



lemma f_huff_polyTime : CookPvsNP.PolyTimeComputable f_huff := by
  obtain ⟨k, hk⟩ := CookPvsNP.polynomial_absorb 1000 4 0
  refine CookPvsNP.stack_program_polytime mainProg .ki .ko f_huff k (fun w => ?_)
  obtain ⟨s, c, hc, he, ho⟩ := exec_mainProg w
  have hk_w := hk w.length
  exact ⟨s, c, by omega, he, ho⟩

end HuffmanTotalPolyTime

-- Source: Solutions/Sol_SyncPrefix_Huffman_decodeEncode_polyTime.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open SyncPrefix.Huffman CookPvsNP

namespace HuffmanNormalizePolyTime

abbrev Sym := Option Bool

inductive SKey where
  | ki
  | ko
  | outRev
  | N
  | K
  | Nrem
  | Krem
  | Q
  | V0
  | C1
  | C2
  | sc
  deriving DecidableEq

instance : Fintype SKey where
  elems := {.ki, .ko, .outRev, .N, .K, .Nrem, .Krem, .Q, .V0, .C1, .C2, .sc}
  complete x := by cases x <;> decide

abbrev Prog := StackProg SKey Sym
abbrev Store := SKey → List Sym

lemma exec_congr {p : Prog} {s t t' : Store} {n : ℕ}
    (h : p.Exec s t n) (ht : t = t') : p.Exec s t' n := ht ▸ h

lemma exec_congr_left {p : Prog} {s s' t : Store} {n : ℕ}
    (h : p.Exec s t n) (hs : s' = s) : p.Exec s' t n := hs ▸ h

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

lemma head?_replicate_isSome (n : ℕ) (a : Sym) (hn : 0 < n) :
    (List.replicate n a).head?.isSome = true := by
  cases n with
  | zero => omega
  | succ n => rfl

lemma head?_replicate_isNone_false (n : ℕ) (a : Sym) (hn : 0 < n) :
    (List.replicate n a).head?.isNone = false := by
  cases n with
  | zero => omega
  | succ n => rfl

lemma drop_eq_getElem_cons {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

/-! ### Unary Emission and Stream Primitives -/

def encUnary (v : ℕ) : List Sym := List.replicate v (some true) ++ [none]

def emitUnaryTo (src dst : SKey) : Prog :=
  .seq (copyProg src dst .sc) (pushProg dst none)

lemma exec_emitUnaryTo (src dst : SKey) (hsd : src ≠ dst) (hst : src ≠ .sc) (hdt : dst ≠ .sc)
    (s : Store) (v : ℕ) (hsrc : s src = List.replicate v (some true)) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 5,
      (emitUnaryTo src dst).Exec s
        (Function.update s dst ((encUnary v).reverse ++ s dst)) c := by
  have e1 := stack_copy src dst .sc hsd hst hdt s hsc
  set s1 := Function.update s dst (s src ++ s dst)
  have e2 := (stack_basic_macros dst s1).1 none
  refine ⟨(6 * (s src).length + 3) + 1 + 1, by simp [hsrc], ?_⟩
  refine exec_congr (StackProg.Exec.seq e1 e2) ?_
  funext k
  cases k <;> simp [s1, hsrc, encUnary, List.reverse_append]

def leadOnes : List Sym → ℕ
  | some _ :: xs => leadOnes xs + 1
  | _ => 0

lemma leadOnes_le : ∀ w : List Sym, leadOnes w ≤ w.length
  | [] => by simp [leadOnes]
  | none :: _ => by simp [leadOnes]
  | some b :: xs => by
    simp only [leadOnes, List.length_cons]
    have := leadOnes_le xs
    omega

def unaryTest (h : Option Sym) : Bool := h.any Option.isSome

lemma head?_drop_of_lt_leadOnes : ∀ (w : List Sym) (i : ℕ), i < leadOnes w →
    unaryTest (w.drop i).head? = true
  | some b :: _, 0, _ => rfl
  | some b :: xs, i + 1, hi => by
    simp only [leadOnes] at hi
    exact head?_drop_of_lt_leadOnes xs i (by omega)
  | [], _, hi => by simp [leadOnes] at hi
  | none :: _, _, hi => by simp [leadOnes] at hi

lemma head?_drop_leadOnes : ∀ w : List Sym,
    unaryTest (w.drop (leadOnes w)).head? = false
  | [] => by simp [leadOnes, unaryTest]
  | none :: _ => by simp [leadOnes, unaryTest]
  | some b :: xs => by
    simp only [leadOnes, List.drop_succ_cons]
    exact head?_drop_leadOnes xs

lemma tail_drop_eq_drop_succ (w : List Sym) (i : ℕ) :
    (w.drop i).tail = w.drop (i + 1) := by
  rw [← List.drop_one, List.drop_drop, add_comm]

def nextWord (w : List Sym) : List Sym := (w.drop (leadOnes w)).tail

def wordAt (w : List Sym) : ℕ → List Sym
  | 0 => w
  | i + 1 => nextWord (wordAt w i)

def valAt (w : List Sym) (i : ℕ) : ℕ := leadOnes (wordAt w i)

lemma length_nextWord_le (w : List Sym) : (nextWord w).length ≤ w.length := by
  simp [nextWord]

lemma length_wordAt_le (w : List Sym) : ∀ i : ℕ, (wordAt w i).length ≤ w.length
  | 0 => le_rfl
  | i + 1 => le_trans (length_nextWord_le (wordAt w i)) (length_wordAt_le w i)

lemma valAt_le_length (w : List Sym) (i : ℕ) : valAt w i ≤ w.length :=
  le_trans (leadOnes_le (wordAt w i)) (length_wordAt_le w i)

def readUnaryAct (src dst : SKey) (_h : SKey → Option Sym) (k : SKey) : StackAct Sym :=
  if k = src then .pop else if k = dst then .push (some true) else .keep

def readUnaryLoop (src dst : SKey) : Prog :=
  .loop (fun h => unaryTest (h src)) (.act (readUnaryAct src dst))

def readUnaryProg (src dst : SKey) : Prog :=
  .seq (readUnaryLoop src dst) (popProg src)

def sReadUnary (src dst : SKey) (s : Store) (i : ℕ) : Store :=
  Function.update (Function.update s src ((s src).drop i))
    dst (List.replicate i (some true))

lemma exec_readUnaryProg_raw (src dst : SKey) (hsd : src ≠ dst)
    (s : Store) (hdst : s dst = []) :
    ∃ c ≤ 3 * leadOnes (s src) + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src (nextWord (s src)))
          dst (List.replicate (leadOnes (s src)) (some true))) c := by
  have hloop : ∃ c1 ≤ leadOnes (s src) * 3 + 1,
      (readUnaryLoop src dst).Exec (sReadUnary src dst s 0)
        (sReadUnary src dst s (leadOnes (s src))) c1 := by
    refine exec_bounded_loop (fun h => unaryTest (h src))
      (.act (readUnaryAct src dst)) (leadOnes (s src)) (sReadUnary src dst s) 1 ?_ ?_ ?_
    · intro i hi
      have hsrc_i : sReadUnary src dst s i src = (s src).drop i := by
        simp [sReadUnary, hsd]
      dsimp only
      rw [hsrc_i]
      exact head?_drop_of_lt_leadOnes (s src) i hi
    · have hsrc_n : sReadUnary src dst s (leadOnes (s src)) src = (s src).drop (leadOnes (s src)) := by
        simp [sReadUnary, hsd]
      dsimp only
      rw [hsrc_n]
      exact head?_drop_leadOnes (s src)
    · intro i _
      refine ⟨1, le_rfl, exec_congr (StackProg.Exec.act (readUnaryAct src dst) (sReadUnary src dst s i)) ?_⟩
      funext k
      by_cases hks : k = src
      · subst hks
        simp [StackProg.applyAct, readUnaryAct, sReadUnary, hsd, StackAct.apply, tail_drop_eq_drop_succ]
      · by_cases hkd : k = dst
        · subst hkd
          simp [StackProg.applyAct, readUnaryAct, sReadUnary, hks, StackAct.apply, List.replicate_succ]
        · simp [StackProg.applyAct, readUnaryAct, sReadUnary, hks, hkd, StackAct.apply]
  have h0 : s = sReadUnary src dst s 0 := by
    funext k
    by_cases hks : k = src
    · subst hks; simp [sReadUnary, hsd]
    · by_cases hkd : k = dst
      · subst hkd; simp [sReadUnary, hdst]
      · simp [sReadUnary, hks, hkd]
  rcases hloop with ⟨c1, hc1, eloop⟩
  have hloop' : ∃ c1 ≤ leadOnes (s src) * 3 + 1,
      (readUnaryLoop src dst).Exec s
        (sReadUnary src dst s (leadOnes (s src))) c1 := ⟨c1, hc1, exec_congr_left eloop h0⟩
  have hpop : ∃ c2 ≤ 1, (popProg src).Exec (sReadUnary src dst s (leadOnes (s src)))
      (Function.update (Function.update s src (nextWord (s src)))
        dst (List.replicate (leadOnes (s src)) (some true))) c2 := by
    refine ⟨1, le_rfl, exec_congr (stack_basic_macros src (sReadUnary src dst s (leadOnes (s src)))).2.1 ?_⟩
    funext k
    by_cases hks : k = src
    · subst hks; simp [sReadUnary, hsd, nextWord]
    · by_cases hkd : k = dst
      · subst hkd; simp [sReadUnary, hks]
      · simp [sReadUnary, hks, hkd]
  exact exec_le_of_le (exec_seq_le hloop' hpop) (by omega)

lemma exec_readUnaryProg_wordAt (src dst : SKey) (hsd : src ≠ dst)
    (s : Store) (w : List Sym) (idx : ℕ)
    (hsrc : s src = wordAt w idx) (hdst : s dst = []) :
    ∃ c ≤ 3 * w.length + 3,
      (readUnaryProg src dst).Exec s
        (Function.update (Function.update s src (wordAt w (idx + 1)))
          dst (List.replicate (valAt w idx) (some true))) c := by
  have hraw := exec_readUnaryProg_raw src dst hsd s hdst
  rw [hsrc] at hraw
  have hv : leadOnes (wordAt w idx) ≤ w.length := valAt_le_length w idx
  exact exec_le_of_le hraw (by omega)


lemma readUnaryOpt_eq (w : List Sym) : readUnaryOpt w = (leadOnes w, nextWord w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | none => rfl
    | some b => simp only [readUnaryOpt, ih, leadOnes, nextWord, List.drop_succ_cons]

def header (n k : ℕ) : List Sym := encUnary n ++ encUnary k

def entryVal (n q : ℕ) (body : List Sym) (i : ℕ) : ℕ :=
  if valAt body i < n then valAt body i else q

def rowPart (n k : ℕ) (body : List Sym) (q a : ℕ) : List Sym :=
  (List.range a).flatMap fun i => encUnary (entryVal n q body (q * k + i))

def tablePart (n k : ℕ) (body : List Sym) (q : ℕ) : List Sym :=
  (List.range q).flatMap fun j => rowPart n k body j k

def normalized (w : List Sym) : List Sym :=
  let n := valAt w 0
  let k := valAt w 1
  header n k ++ tablePart n k (wordAt w 2) n

def initProg : Prog :=
  .seq (readUnaryProg .ki .N)
    (.seq (readUnaryProg .ki .K)
      (.seq (emitUnaryTo .N .outRev)
        (.seq (emitUnaryTo .K .outRev) (copyProg .N .Nrem .sc))))

def rowStore (n k : ℕ) (body : List Sym) (q : ℕ) : Store := fun j =>
  if j = .ki then wordAt body (q * k)
  else if j = .N then List.replicate n (some true)
  else if j = .K then List.replicate k (some true)
  else if j = .Nrem then List.replicate (n - q) (some true)
  else if j = .Q then List.replicate q (some true)
  else if j = .outRev then (tablePart n k body q).reverse ++ (header n k).reverse
  else []

def innerStore (n k : ℕ) (body : List Sym) (q a : ℕ) : Store := fun j =>
  if j = .ki then wordAt body (q * k + a)
  else if j = .N then List.replicate n (some true)
  else if j = .K then List.replicate k (some true)
  else if j = .Nrem then List.replicate (n - q - 1) (some true)
  else if j = .Krem then List.replicate (k - a) (some true)
  else if j = .Q then List.replicate q (some true)
  else if j = .outRev then (rowPart n k body q a).reverse ++
    (tablePart n k body q).reverse ++ (header n k).reverse
  else []

def prepCompareProg : Prog :=
  .seq (copyProg .V0 .C1 .sc)
    (.seq (copyProg .N .C2 .sc)
      (syncPopProg .C1 .C2))

def cleanCompareProg : Prog :=
  .seq (clearProg .C1) (clearProg .C2)

def isLtTest (h : SKey → Option Sym) : Bool := (h .C2).isSome

def branchLtVN (trueProg falseProg : Prog) : Prog :=
  .seq prepCompareProg
    (.branch isLtTest (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg))

def cmpStore (s : Store) (v q : ℕ) : Store :=
  Function.update (Function.update s .C1 (List.replicate (v - q) (some true)))
    .C2 (List.replicate (q - v) (some true))

lemma isLtTest_cmpStore (s : Store) (v q : ℕ) :
    isLtTest (fun k => (cmpStore s v q k).head?) = decide (v < q) := by
  by_cases h : v < q
  · simp [isLtTest, cmpStore, h, head?_replicate_isSome, Nat.sub_pos_of_lt h]
  · simp [isLtTest, cmpStore, h, Nat.sub_eq_zero_of_le (by omega : q ≤ v)]

lemma exec_prepCompareProg (s : Store) (v q : ℕ)
    (hV0 : s .V0 = List.replicate v (some true))
    (hN : s .N = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = []) :
    ∃ c ≤ 6 * v + 9 * q + 9,
      prepCompareProg.Exec s (cmpStore s v q) c := by
  have hc1 := stack_copy SKey.V0 SKey.C1 SKey.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s .C1 (s .V0 ++ s .C1)
  have e1 : ∃ c ≤ 6 * v + 3, (copyProg .V0 .C1 .sc).Exec s s1 c :=
    ⟨6 * (s .V0).length + 3, by simp [hV0], hc1⟩
  have hc2 := stack_copy SKey.N SKey.C2 SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, hsc])
  set s2 := Function.update s1 .C2 (s1 .N ++ s1 .C2)
  have e2 : ∃ c ≤ 6 * q + 3, (copyProg .N .C2 .sc).Exec s1 s2 c :=
    ⟨6 * (s1 .N).length + 3, by simp [s1, hN], hc2⟩
  have hsync := stack_sync_pop SKey.C1 SKey.C2 (by decide) s2
  have hs2_C1 : (s2 .C1).length = v := by simp [s2, s1, hV0, hC1]
  have hs2_C2 : (s2 .C2).length = q := by simp [s2, s1, hN, hC2]
  have e3 : ∃ c ≤ 3 * q + 1, (syncPopProg .C1 .C2).Exec s2 (cmpStore s v q) c := by
    refine ⟨3 * min (s2 .C1).length (s2 .C2).length + 1, ?_, exec_congr hsync ?_⟩
    · rw [hs2_C1, hs2_C2]
      have : min v q ≤ q := Nat.min_le_right v q
      omega
    · funext k
      cases k <;> simp [s2, s1, cmpStore, hV0, hN, hC1, hC2, List.drop_replicate] <;> omega
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 e3)) (by omega)

lemma exec_cleanCompareProg (s : Store) (v q : ℕ)
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) :
    ∃ c ≤ 3 * v + 3 * q + 3,
      cleanCompareProg.Exec (cmpStore s v q) s c := by
  have hc1 := (stack_basic_macros SKey.C1 (cmpStore s v q)).2.2
  set s1 := Function.update (cmpStore s v q) .C1 []
  have e1 : ∃ c ≤ 3 * v + 1, (clearProg .C1).Exec (cmpStore s v q) s1 c := by
    refine ⟨3 * (cmpStore s v q .C1).length + 1, ?_, hc1⟩
    simp [cmpStore]
  have hc2 := (stack_basic_macros SKey.C2 s1).2.2
  have e2 : ∃ c ≤ 3 * q + 1, (clearProg .C2).Exec s1 s c := by
    refine ⟨3 * (s1 .C2).length + 1, ?_, exec_congr hc2 ?_⟩
    · simp [s1, cmpStore]
    · funext k
      cases k <;> simp [s1, cmpStore, hC1, hC2]
  exact exec_le_of_le (exec_seq_le e1 e2) (by omega)

lemma exec_branchLtVN_true (trueProg falseProg : Prog) (s t : Store) (v q B : ℕ)
    (hV0 : s .V0 = List.replicate v (some true))
    (hN : s .N = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = [])
    (heq : v < q) (ht : ∃ c ≤ B, trueProg.Exec s t c) :
    ∃ c ≤ 9 * v + 12 * q + 15 + B,
      (branchLtVN trueProg falseProg).Exec s t c := by
  have e1 := exec_prepCompareProg s v q hV0 hN hC1 hC2 hsc
  have htest : isLtTest (fun k => (cmpStore s v q k).head?) = true := by
    rw [isLtTest_cmpStore, decide_eq_true_eq]
    exact heq
  have e_clean := exec_cleanCompareProg s v q hC1 hC2
  have e_br := exec_branch_true_le isLtTest
    (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg)
    htest (exec_seq_le e_clean ht)
  exact exec_le_of_le (exec_seq_le e1 e_br) (by omega)

lemma exec_branchLtVN_false (trueProg falseProg : Prog) (s t : Store) (v q B : ℕ)
    (hV0 : s .V0 = List.replicate v (some true))
    (hN : s .N = List.replicate q (some true))
    (hC1 : s .C1 = []) (hC2 : s .C2 = []) (hsc : s .sc = [])
    (hne : ¬ v < q) (hf : ∃ c ≤ B, falseProg.Exec s t c) :
    ∃ c ≤ 9 * v + 12 * q + 15 + B,
      (branchLtVN trueProg falseProg).Exec s t c := by
  have e1 := exec_prepCompareProg s v q hV0 hN hC1 hC2 hsc
  have htest : isLtTest (fun k => (cmpStore s v q k).head?) = false := by
    rw [isLtTest_cmpStore, decide_eq_false_iff_not]
    exact hne
  have e_clean := exec_cleanCompareProg s v q hC1 hC2
  have e_br := exec_branch_false_le isLtTest
    (.seq cleanCompareProg trueProg) (.seq cleanCompareProg falseProg)
    htest (exec_seq_le e_clean hf)
  exact exec_le_of_le (exec_seq_le e1 e_br) (by omega)


def innerBody : Prog :=
  .seq (popProg .Krem)
    (.seq (readUnaryProg .ki .V0)
      (.seq (branchLtVN (emitUnaryTo .V0 .outRev) (emitUnaryTo .Q .outRev))
        (clearProg .V0)))

def innerLoop : Prog := .loop (fun h => (h .Krem).isSome) innerBody

def rowBody : Prog :=
  .seq (popProg .Nrem)
    (.seq (copyProg .K .Krem .sc)
      (.seq innerLoop (pushProg .Q (some true))))

def rowLoop : Prog := .loop (fun h => (h .Nrem).isSome) rowBody

def mainProg : Prog :=
  .seq initProg (.seq rowLoop (transferProg .outRev (fun j => decide (j = .ko))))

lemma rowPart_succ (n k : ℕ) (body : List Sym) (q a : ℕ) :
    rowPart n k body q (a + 1) = rowPart n k body q a ++
      encUnary (entryVal n q body (q * k + a)) := by
  simp [rowPart, List.range_succ]

lemma tablePart_succ (n k : ℕ) (body : List Sym) (q : ℕ) :
    tablePart n k body (q + 1) = tablePart n k body q ++ rowPart n k body q k := by
  simp [tablePart, List.range_succ]

lemma exec_initProg (w : List Sym) :
    let n := valAt w 0
    let k := valAt w 1
    let body := wordAt w 2
    ∃ c ≤ 24 * w.length + 23,
      initProg.Exec (fun j => if j = .ki then w else []) (rowStore n k body 0) c := by
  intro n k body
  set s0 : Store := fun j => if j = .ki then w else []
  have e1 := exec_readUnaryProg_wordAt .ki .N (by decide) s0 w 0 rfl rfl
  set s1 := Function.update (Function.update s0 .ki (wordAt w 1))
    .N (List.replicate n (some true))
  have e2 := exec_readUnaryProg_wordAt .ki .K (by decide) s1 w 1
    (by simp [s1]) (by simp [s1, s0])
  set s2 := Function.update (Function.update s1 .ki body) .K (List.replicate k (some true))
  have e3 := exec_emitUnaryTo .N .outRev (by decide) (by decide) (by decide)
    s2 n (by simp [s2, s1]) (by simp [s2, s1, s0])
  set s3 := Function.update s2 .outRev ((encUnary n).reverse ++ s2 .outRev)
  have e4 := exec_emitUnaryTo .K .outRev (by decide) (by decide) (by decide)
    s3 k (by simp [s3, s2]) (by simp [s3, s2, s1, s0])
  set s4 := Function.update s3 .outRev ((encUnary k).reverse ++ s3 .outRev)
  have hc5 := stack_copy SKey.N SKey.Nrem SKey.sc (by decide) (by decide) (by decide) s4
    (by simp [s4, s3, s2, s1, s0])
  have e5 : ∃ c ≤ 6 * n + 3, (copyProg .N .Nrem .sc).Exec s4 (rowStore n k body 0) c := by
    refine ⟨6 * (s4 .N).length + 3, by simp [s4, s3, s2, s1], exec_congr hc5 ?_⟩
    funext j
    cases j <;> simp [s4, s3, s2, s1, s0, rowStore, tablePart, header, wordAt,
      List.reverse_append, List.append_assoc]
  have hn : n ≤ w.length := valAt_le_length w 0
  have hk : k ≤ w.length := valAt_le_length w 1
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2
    (exec_seq_le e3 (exec_seq_le e4 e5)))) (by omega)

lemma exec_innerBody (n k : ℕ) (body : List Sym) (q a : ℕ) :
    ∃ c ≤ 21 * body.length + 12 * n + 6 * q + 28,
      innerBody.Exec (innerStore n k body q a) (innerStore n k body q (a + 1)) c := by
  set s0 := innerStore n k body q a
  have hp1 := (stack_basic_macros SKey.Krem s0).2.1
  set s1 := Function.update s0 .Krem (s0 .Krem).tail
  have e1 : ∃ c ≤ 1, (popProg .Krem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have e2 := exec_readUnaryProg_wordAt .ki .V0 (by decide) s1 body (q * k + a)
    (by simp [s1, s0, innerStore]) (by simp [s1, s0, innerStore])
  set v := valAt body (q * k + a)
  have hvL : v ≤ body.length := valAt_le_length body _
  set s2 := Function.update (Function.update s1 .ki (wordAt body (q * k + a + 1)))
    .V0 (List.replicate v (some true))
  set s3 := Function.update s2 .outRev
    ((encUnary (entryVal n q body (q * k + a))).reverse ++ s2 .outRev)
  have hV : s2 .V0 = List.replicate v (some true) := by simp [s2]
  have hN : s2 .N = List.replicate n (some true) := by simp [s2, s1, s0, innerStore]
  have hQ : s2 .Q = List.replicate q (some true) := by simp [s2, s1, s0, innerStore]
  have hC1 : s2 .C1 = [] := by simp [s2, s1, s0, innerStore]
  have hC2 : s2 .C2 = [] := by simp [s2, s1, s0, innerStore]
  have hsc : s2 .sc = [] := by simp [s2, s1, s0, innerStore]
  have e3 : ∃ c ≤ 15 * body.length + 12 * n + 6 * q + 20,
      (branchLtVN (emitUnaryTo .V0 .outRev) (emitUnaryTo .Q .outRev)).Exec s2 s3 c := by
    by_cases hv : v < n
    · have ee := exec_emitUnaryTo .V0 .outRev (by decide) (by decide) (by decide) s2 v hV hsc
      have ee' : ∃ c ≤ 6 * v + 5, (emitUnaryTo .V0 .outRev).Exec s2 s3 c := by
        have he : entryVal n q body (q * k + a) = v := if_pos hv
        simpa only [s3, he] using ee
      exact exec_le_of_le (exec_branchLtVN_true _ _ s2 s3 v n _
        hV hN hC1 hC2 hsc hv ee') (by omega)
    · have ee := exec_emitUnaryTo .Q .outRev (by decide) (by decide) (by decide) s2 q hQ hsc
      have ee' : ∃ c ≤ 6 * q + 5, (emitUnaryTo .Q .outRev).Exec s2 s3 c := by
        have he : entryVal n q body (q * k + a) = q := if_neg hv
        simpa only [s3, he] using ee
      exact exec_le_of_le (exec_branchLtVN_false _ _ s2 s3 v n _
        hV hN hC1 hC2 hsc hv ee') (by omega)
  have hc4 := (stack_basic_macros SKey.V0 s3).2.2
  have e4 : ∃ c ≤ 3 * body.length + 1, (clearProg .V0).Exec s3
      (innerStore n k body q (a + 1)) c := by
    refine ⟨3 * (s3 .V0).length + 1, ?_, exec_congr hc4 ?_⟩
    · simp [s3, s2]
      omega
    · funext j
      cases j <;> simp [s3, s2, s1, s0, innerStore, rowPart_succ,
        List.reverse_append, List.append_assoc, Nat.sub_sub, Nat.add_assoc]
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4))) (by omega)

lemma exec_innerLoop (n k : ℕ) (body : List Sym) (q : ℕ) :
    ∃ c ≤ k * (21 * body.length + 12 * n + 6 * q + 30) + 1,
      innerLoop.Exec (innerStore n k body q 0) (innerStore n k body q k) c := by
  apply exec_bounded_loop (fun h => (h .Krem).isSome) innerBody k
    (innerStore n k body q) (21 * body.length + 12 * n + 6 * q + 28)
  · intro a ha
    simp [innerStore, head?_replicate_isSome, Nat.sub_pos_of_lt ha]
  · simp [innerStore]
  · intro a ha
    exact exec_innerBody n k body q a

lemma exec_rowBody (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q < n) :
    ∃ c ≤ k * (21 * body.length + 18 * n + 36) + 9,
      rowBody.Exec (rowStore n k body q) (rowStore n k body (q + 1)) c := by
  set s0 := rowStore n k body q
  have hp1 := (stack_basic_macros SKey.Nrem s0).2.1
  set s1 := Function.update s0 .Nrem (s0 .Nrem).tail
  have e1 : ∃ c ≤ 1, (popProg .Nrem).Exec s0 s1 c := ⟨1, le_rfl, hp1⟩
  have hc2 := stack_copy SKey.K SKey.Krem SKey.sc (by decide) (by decide) (by decide) s1
    (by simp [s1, s0, rowStore])
  have e2 : ∃ c ≤ 6 * k + 3, (copyProg .K .Krem .sc).Exec s1
      (innerStore n k body q 0) c := by
    refine ⟨6 * (s1 .K).length + 3, by simp [s1, s0, rowStore], exec_congr hc2 ?_⟩
    funext j
    cases j <;> simp [s1, s0, rowStore, innerStore, rowPart]
  have e3 := exec_innerLoop n k body q
  have hp4 := (stack_basic_macros SKey.Q (innerStore n k body q k)).1 (some true)
  have e4 : ∃ c ≤ 1, (pushProg .Q (some true)).Exec (innerStore n k body q k)
      (rowStore n k body (q + 1)) c := by
    refine ⟨1, le_rfl, exec_congr hp4 ?_⟩
    funext j
    cases j <;> simp [innerStore, rowStore, tablePart_succ, List.reverse_append,
      List.append_assoc, List.replicate_succ, Nat.sub_sub, Nat.add_mul]
  have hq' : k * (21 * body.length + 12 * n + 6 * q + 30) ≤
      k * (21 * body.length + 18 * n + 30) :=
    Nat.mul_le_mul_left k (by omega)
  exact exec_le_of_le (exec_seq_le e1 (exec_seq_le e2 (exec_seq_le e3 e4)))
    (by nlinarith)

lemma exec_rowLoop (n k : ℕ) (body : List Sym) :
    ∃ c ≤ n * (k * (21 * body.length + 18 * n + 36) + 11) + 1,
      rowLoop.Exec (rowStore n k body 0) (rowStore n k body n) c := by
  apply exec_bounded_loop (fun h => (h .Nrem).isSome) rowBody n
    (rowStore n k body) (k * (21 * body.length + 18 * n + 36) + 9)
  · intro q hq
    simp [rowStore, head?_replicate_isSome, Nat.sub_pos_of_lt hq]
  · simp [rowStore]
  · intro q hq
    exact exec_rowBody n k body q hq

lemma entryVal_lt (n q : ℕ) (body : List Sym) (i : ℕ) (hq : q < n) :
    entryVal n q body i < n := by
  unfold entryVal
  split <;> assumption

lemma rowPart_length_le (n k : ℕ) (body : List Sym) (q a : ℕ) (hq : q < n) :
    (rowPart n k body q a).length ≤ a * n := by
  induction a with
  | zero => simp [rowPart]
  | succ a ih =>
    rw [rowPart_succ]
    simp only [List.length_append, encUnary, List.length_replicate, List.length_singleton]
    have hv := entryVal_lt n q body (q * k + a) hq
    nlinarith

lemma tablePart_length_le (n k : ℕ) (body : List Sym) (q : ℕ) (hq : q ≤ n) :
    (tablePart n k body q).length ≤ q * k * n := by
  induction q with
  | zero => simp [tablePart]
  | succ q ih =>
    rw [tablePart_succ, List.length_append]
    have h₁ := ih (by omega)
    have h₂ := rowPart_length_le n k body q k (by omega)
    nlinarith

lemma exec_mainProg (w : List Sym) :
    ∃ s c, c ≤ 160 * (w.length + 1) ^ 3 ∧
      mainProg.Exec (fun j => if j = .ki then w else []) s c ∧ s .ko = normalized w := by
  set M := w.length + 1
  set n := valAt w 0
  set k := valAt w 1
  set body := wordAt w 2
  have hM : 1 ≤ M := by omega
  have hn : n ≤ w.length := valAt_le_length w 0
  have hk : k ≤ w.length := valAt_le_length w 1
  have hb : body.length ≤ w.length := length_wordAt_le w 2
  have hnM : n ≤ M := by omega
  have hkM : k ≤ M := by omega
  have hbM : body.length ≤ M := by omega
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ≤ M ^ 3 := by nlinarith [Nat.mul_le_mul_left M hM2]
  have h1M3 : 1 ≤ M ^ 3 := hM.trans hM3
  have hinner : 21 * body.length + 18 * n + 36 ≤ 75 * M := by omega
  have hprod := Nat.mul_le_mul hnM (Nat.mul_le_mul hkM hinner)
  have hrow : n * (k * (21 * body.length + 18 * n + 36) + 11) + 1 ≤ 87 * M ^ 3 := by
    nlinarith
  have htable := tablePart_length_le n k body n le_rfl
  have hnk := Nat.mul_le_mul hnM hkM
  have hnkn := Nat.mul_le_mul hnk hnM
  have hout : ((rowStore n k body n) .outRev).length ≤ 5 * M ^ 3 := by
    simp only [rowStore]
    simp only [reduceCtorEq, ↓reduceIte, List.length_append, List.length_reverse,
      header, encUnary, List.length_replicate, List.length_singleton]
    nlinarith
  have e1 := exec_initProg w
  have e2 := exec_rowLoop n k body
  set s2 := rowStore n k body n
  set s3 := transferStore .outRev (fun j => decide (j = .ko)) s2
  have ht := stack_transfer SKey.outRev (fun j => decide (j = .ko)) s2
  have e3 : ∃ c ≤ 3 * (s2 .outRev).length + 1,
      (transferProg .outRev (fun j => decide (j = .ko))).Exec s2 s3 c :=
    ⟨_, le_rfl, ht⟩
  obtain ⟨c, hc, he⟩ := exec_seq_le e1 (exec_seq_le e2 e3)
  refine ⟨s3, c, ?_, he, ?_⟩
  · change (s2 .outRev).length ≤ 5 * M ^ 3 at hout
    omega
  · simp [s3, s2, transferStore, rowStore, normalized, n, k, body,
      List.reverse_append, List.reverse_reverse]

lemma normalized_polyTime : PolyTimeComputable normalized := by
  obtain ⟨d, hd⟩ := polynomial_absorb 160 3 0
  apply stack_program_polytime mainProg .ki .ko normalized d
  intro w
  obtain ⟨s, c, hc, he, ho⟩ := exec_mainProg w
  exact ⟨s, c, by have := hd w.length; omega, he, ho⟩

lemma wordAt_succ_eq_wordAt_nextWord (w : List Sym) (idx : ℕ) :
    wordAt w (idx + 1) = wordAt (nextWord w) idx := by
  induction idx generalizing w with
  | zero => rfl
  | succ idx ih =>
    change nextWord (wordAt w (idx + 1)) = nextWord (wordAt (nextWord w) idx)
    rw [ih w]

lemma getD_readUnaryList (m : ℕ) (w : List Sym) (i : ℕ) (hi : i < m) :
    (readUnaryList m w).1.getD i 0 = valAt w i := by
  induction m generalizing w i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero => simp [readUnaryList, readUnaryOpt_eq, valAt, wordAt, List.getD_cons_zero]
    | succ i =>
      rw [readUnaryList, readUnaryOpt_eq]
      simp only [List.getD_cons_succ]
      rw [ih (nextWord w) i (by omega)]
      simp [valAt, wordAt_succ_eq_wordAt_nextWord]

lemma flatMap_finRange_eq_flatMap_range {α : Type} (n : ℕ) (g : ℕ → List α) :
    (List.finRange n).flatMap (fun x : Fin n => g x.val) = (List.range n).flatMap g := by
  have hm : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [← List.flatMap_map, hm]

lemma tablePart_eq (n k : ℕ) (body : List Sym) :
    tablePart n k body n =
      (List.finRange n).flatMap fun q => (List.finRange k).flatMap fun a =>
        encUnary ((if h : (readUnaryList (n * k) body).1.getD (q.val * k + a.val) 0 < n then
          ⟨(readUnaryList (n * k) body).1.getD (q.val * k + a.val) 0, h⟩ else q : Fin n).val) := by
  unfold tablePart
  rw [← flatMap_finRange_eq_flatMap_range]
  apply List.flatMap_congr
  intro q hq
  unfold rowPart
  rw [← flatMap_finRange_eq_flatMap_range]
  apply List.flatMap_congr
  intro a ha
  have hi : q.val * k + a.val < n * k := by
    have hq' := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr q.isLt)
    have ha' := a.isLt
    nlinarith
  rw [getD_readUnaryList (n * k) body _ hi]
  by_cases h : valAt body (q.val * k + a.val) < n <;> simp [entryVal, h]

lemma normalized_eq_encode (w : List Sym) : normalized w = (decodeAutomaton w).encode := by
  unfold normalized
  simp only [valAt, wordAt]
  unfold decodeAutomaton
  rw [readUnaryOpt_eq w]
  dsimp only
  rw [readUnaryOpt_eq (nextWord w)]
  dsimp only
  rw [tablePart_eq]
  simp only [Automaton.encode, header, encUnary, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append]

/-- Decoding and re-encoding the total unary automaton format is polynomial-time computable. -/
theorem decodeEncode_polyTime :
    PolyTimeComputable (fun w => (decodeAutomaton w).encode) := by
  have heq : (fun w => (decodeAutomaton w).encode) = normalized :=
    funext fun w => (normalized_eq_encode w).symm
  rw [heq]
  exact normalized_polyTime

end HuffmanNormalizePolyTime

-- Source: Solutions/Submit_SyncPrefix_Huffman_huffmanEncodeMap_polyTime.lean
open SyncPrefix.Huffman

theorem solution : CookPvsNP.PolyTimeComputable huffmanEncodeMap := by
  have hcomp := CookPvsNP.polyTimeComputable_comp
    (fun w ↦ (decodeAutomaton w).encode) HuffmanTotalFormula.f_huff
    HuffmanNormalizePolyTime.decodeEncode_polyTime HuffmanTotalPolyTime.f_huff_polyTime
  have heq :
      (HuffmanTotalFormula.f_huff ∘ (fun w ↦ (decodeAutomaton w).encode)) =
        huffmanEncodeMap := by
    funext w
    exact HuffmanTotalFormula.f_huff_encode (decodeAutomaton w)
  rwa [heq] at hcomp
