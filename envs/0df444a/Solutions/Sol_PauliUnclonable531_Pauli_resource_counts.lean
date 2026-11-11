-- Prove2me | solution 1 for PauliUnclonable531.Pauli.resource_counts
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:23:52.425896+00:00
-- url     : https://prove2.me/submissions/286ae205-dda1-4e8d-812a-38ba6bce92ca

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Counts

open PauliUnclonable531.Pauli

variable {n : ℕ}

/-- The scan step used by `pivot`. -/
def scanStep (k : Key n) (p : Option (Fin n)) (j : Fin n) : Option (Fin n) :=
  match p with
  | some i => some i
  | none => if active k.val j then some j else none

lemma foldl_scan_some (k : Key n) (i : Fin n) (l : List (Fin n)) :
    l.foldl (scanStep k) (some i) = some i := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons]; exact ih

lemma foldl_scan_none (k : Key n) (l : List (Fin n)) :
    l.foldl (scanStep k) none = l.find? (active k.val) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.find?_cons]
    by_cases ha : active k.val a = true
    · simp only [scanStep, ha, if_true]
      exact foldl_scan_some k a l
    · simp only [Bool.not_eq_true] at ha
      simp only [scanStep, ha]
      exact ih

lemma pivot_eq_find (k : Key n) : pivot k = (List.finRange n).find? (active k.val) :=
  foldl_scan_none k _

lemma exists_active (k : Key n) : ∃ j, active k.val j = true := by
  by_contra h
  simp only [not_exists, Bool.not_eq_true] at h
  apply k.property
  have h1 : ∀ j, k.val.1 j = 0 ∧ k.val.2 j = 0 := by
    intro j
    have := h j
    simp only [active, decide_eq_false_iff_not, not_or, not_not] at this
    exact this
  exact Prod.ext (funext fun j => (h1 j).1) (funext fun j => (h1 j).2)

lemma pivot_spec (k : Key n) : ∃ j, pivot k = some j ∧ active k.val j = true ∧
    ∀ i : Fin n, i < j → active k.val i = false := by
  rw [pivot_eq_find]
  obtain ⟨j0, hj0⟩ := exists_active k
  have hsome : ((List.finRange n).find? (active k.val)).isSome := by
    rw [List.find?_isSome]
    exact ⟨j0, List.mem_finRange j0, hj0⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨j, hj, ?_⟩
  rw [List.find?_eq_some_iff_getElem] at hj
  obtain ⟨hpj, i0, hi0, hget, hbefore⟩ := hj
  refine ⟨hpj, fun i hi => ?_⟩
  have hjv : j.val = i0 := by
    rw [← hget, List.getElem_finRange]; rfl
  have hilt : i.val < i0 := by rw [← hjv]; exact hi
  have := hbefore i.val hilt
  rw [List.getElem_finRange] at this
  simpa using this

lemma card_tape (k : Key n) (hn : 1 ≤ n) : Fintype.card (Tape k) = 2 ^ (n - 1) := by
  obtain ⟨p, hp, -, -⟩ := pivot_spec k
  have e : Tape k ≃ ({j : Fin n // j ≠ p} → Fin 2) :=
    { toFun := fun r j => r.val j.val
      invFun := fun f => ⟨fun j => if h : j = p then 0 else f ⟨j, h⟩, by
        intro j hj; rw [hp] at hj; cases hj; simp⟩
      left_inv := by
        intro r
        apply Subtype.ext
        funext j
        by_cases h : j = p
        · subst h; simp [r.property j hp]
        · simp [h]
      right_inv := by
        intro f
        funext j
        simp [j.property] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Fintype.card_fin]

lemma length_others (p : Fin n) :
    ((List.finRange n).filter (fun j => decide (some j ≠ some p))).length = n - 1 := by
  have hpred : (fun j : Fin n => decide (some j ≠ some p)) = fun j => !(j == p) := by
    funext j; by_cases h : j = p <;> simp [h]
  rw [hpred]
  have h := List.length_eq_countP_add_countP (p := fun j : Fin n => j == p) (l := List.finRange n)
  have hc : List.countP (fun j : Fin n => j == p) (List.finRange n) = 1 := by
    rw [← List.count]
    exact List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange p)
  rw [List.length_finRange, hc] at h
  rw [← List.countP_eq_length_filter]
  have : List.countP (fun j : Fin n => !(j == p)) (List.finRange n) =
      List.countP (fun a : Fin n => decide ¬(a == p) = true) (List.finRange n) := by
    congr 1; funext j; by_cases h : j = p <;> simp [h]
  omega

end PauliUnclonable531.Pauli.Counts

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Counts in
theorem solution (n : ℕ) (hn : 1 ≤ n) (k : Key n) :
    (∃ j, pivot k = some j ∧ active k.val j = true ∧
      ∀ i : Fin n, i < j → active k.val i = false) ∧
    Fintype.card (Tape k) = 2^(n-1) ∧
    fairCount (encProgram k) = n-1 ∧ preparationCount (encProgram k) = n ∧
    gateCount (encProgram k) ≤ 2*n ∧ encBitCost k ≤ 100*(n+1)^2 ∧
    (decProgram k).length ≤ n ∧ decBitCost k ≤ 100*(n+1)^2 := by
  obtain ⟨p, hp, hpa, hmin⟩ := pivot_spec k
  set others := (List.finRange n).filter (fun j => decide (some j ≠ some p)) with hothers
  have hlo : others.length = n - 1 := length_others p
  have hprog : encProgram k = others.map EncInstruction.fair ++ [.loadMessage] ++
      (others.filter (active k.val)).map EncInstruction.xorBit ++ [.storePivot] ++
      (List.finRange n).map EncInstruction.prepare ++ (List.finRange n).flatMap (fun j =>
        if k.val.1 j = 0 then [] else
          [.gate j .H] ++ if k.val.2 j = 0 then [] else [.gate j .S]) := by
    simp only [encProgram, hp, hothers]
  have hgates : ∀ l : List (Fin n), (l.flatMap (fun j =>
        if k.val.1 j = 0 then ([] : List (EncInstruction n)) else
          [.gate j .H] ++ if k.val.2 j = 0 then [] else [.gate j .S])).length ≤ 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have : (if k.val.1 a = 0 then ([] : List (EncInstruction n)) else
          [.gate a .H] ++ if k.val.2 a = 0 then [] else [.gate a .S]).length ≤ 2 := by
        split_ifs <;> simp
      omega
  have hxor : (others.filter (active k.val)).length ≤ n - 1 :=
    (List.length_filter_le _ _).trans hlo.le
  have hlen : (encProgram k).length ≤ 5 * n := by
    rw [hprog]
    simp only [List.length_append, List.length_map, List.length_singleton, List.length_finRange]
    have := hgates (List.finRange n)
    rw [List.length_finRange] at this
    omega
  have hdec : (decProgram k).length ≤ n := by
    simp only [decProgram, List.length_map]
    exact (List.length_filter_le _ _).trans (List.length_finRange).le
  refine ⟨⟨p, hp, hpa, hmin⟩, card_tape k hn, ?_, ?_, ?_, ?_, hdec, ?_⟩
  · rw [fairCount, hprog]
    simp only [List.filter_append, List.length_append, List.filter_map, List.length_map]
    simp [Function.comp_def, hlo, List.filter_flatMap]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> simp
  · rw [preparationCount, hprog]
    simp only [List.filter_append, List.length_append, List.filter_map, List.length_map]
    simp [Function.comp_def, List.filter_flatMap]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    split_ifs <;> simp
  · rw [gateCount, hprog]
    simp only [List.filter_append, List.length_append, List.filter_map, List.length_map]
    have := (List.length_filter_le (fun i : EncInstruction n => match i with
      | .gate _ _ => true | _ => false) _).trans (hgates (List.finRange n))
    rw [List.length_finRange] at this
    simp only [Function.comp_def, List.filter_singleton, List.length_nil, List.filter_false] at this ⊢
    simp at this ⊢
    omega
  · rw [encBitCost, List.length_finRange]
    have h1 : n + (encProgram k).length + 1 ≤ 10 * (n + 1) := by omega
    calc 10 * (n + 1) * (n + (encProgram k).length + 1) ≤ 10 * (n + 1) * (10 * (n + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ = 100 * (n + 1) ^ 2 := by ring
  · rw [decBitCost, List.length_finRange]
    have h1 : n + 2 * (decProgram k).length + 1 ≤ 10 * (n + 1) := by omega
    calc 10 * (n + 1) * (n + 2 * (decProgram k).length + 1) ≤ 10 * (n + 1) * (10 * (n + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ = 100 * (n + 1) ^ 2 := by ring
