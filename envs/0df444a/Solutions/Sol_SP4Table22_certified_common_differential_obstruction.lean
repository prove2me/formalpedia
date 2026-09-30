-- Prove2me | solution 1 for SP4Table22.certified_common_differential_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T04:24:14.731027+00:00
-- url     : https://prove2.me/submissions/8c5c6350-61ae-4c1c-8f52-05966b0041fa

import Mathlib
import Definitions.Def_SP4Table22Certificates
import Definitions.Def_Smooth4AlgebraHomology

set_option autoImplicit false

namespace Smooth4SupportCover

private theorem rank_add_le {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  have h : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro x ⟨v, rfl⟩
    have hv : (A + B).mulVecLin v = A.mulVecLin v + B.mulVecLin v := by
      simp [Matrix.mulVecLin]
    rw [hv]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono h).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- An explicitly checked bipartite vertex cover bounds matrix rank over any field.
Rows and columns are separate vertex sets, even when their index types coincide. -/
theorem rank_le_cover {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) (rows : Finset m) (cols : Finset n)
    (hcover : ∀ i j, i ∉ rows → j ∉ cols → A i j = 0) :
    A.rank ≤ rows.card + cols.card := by
  classical
  let R : Matrix m n K := fun i j => if i ∈ rows then A i j else 0
  let C : Matrix m n K := fun i j => if i ∈ rows then 0 else A i j
  have hsplit : A = R + C := by
    ext i j
    change A i j = (if i ∈ rows then A i j else 0) +
      (if i ∈ rows then 0 else A i j)
    by_cases hi : i ∈ rows <;> simp [hi]
  have hR : R.rank ≤ rows.card := by
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro i hi
    change i ∉ rows at hi
    ext j
    change (if i ∈ rows then A i j else 0) = 0
    simp [hi]
  have hC : C.rank ≤ cols.card := by
    rw [← Matrix.rank_transpose C]
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro j hj
    change j ∉ cols at hj
    ext i
    change (if i ∈ rows then 0 else A i j) = 0
    by_cases hi : i ∈ rows
    · simp [hi]
    · simp [hi, hcover i j hi hj]
  rw [hsplit]
  exact (rank_add_le R C).trans (Nat.add_le_add hR hC)

/-- The homology rank identity for a genuinely square-zero coordinate differential. -/
theorem homology_rank_identity {K ι : Type*} [Field K] [Fintype ι]
    (D : Matrix ι ι K) (h_square : D.mulVecLin.comp D.mulVecLin = 0) :
    Module.finrank K (Smooth4Algebra.Homology D.mulVecLin) + 2 * D.rank =
      Fintype.card ι := by
  have h_boundary : LinearMap.range D.mulVecLin ≤ LinearMap.ker D.mulVecLin := by
    rintro x ⟨y, rfl⟩
    have h := LinearMap.congr_fun h_square y
    simpa using h
  have h_dim_boundary :
      Module.finrank K (Smooth4Algebra.boundariesInCycles D.mulVecLin) =
        Module.finrank K (LinearMap.range D.mulVecLin) :=
    (Submodule.comapSubtypeEquivOfLe h_boundary).finrank_eq
  have h_homology :=
    (Smooth4Algebra.boundariesInCycles D.mulVecLin).finrank_quotient_add_finrank
  change Module.finrank K (Smooth4Algebra.Homology D.mulVecLin) +
    Module.finrank K (Smooth4Algebra.boundariesInCycles D.mulVecLin) =
    Module.finrank K (LinearMap.ker D.mulVecLin) at h_homology
  rw [h_dim_boundary] at h_homology
  have h_nullity := D.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at h_nullity
  change Module.finrank K (Smooth4Algebra.Homology D.mulVecLin) +
    2 * Module.finrank K (LinearMap.range D.mulVecLin) = Fintype.card ι
  omega

end Smooth4SupportCover

open Smooth4SupportCover

/-- A support cover for the total matrix and a separate cover for its unrestricted
perturbation combine by a minimum, then give a lower bound for actual homology.
No coefficient search, chosen barcode basis, or square-zero condition on the two
summands separately is assumed. -/
theorem SP4Table22.support_budget {K ι : Type*} [Field K] [Fintype ι]
    (A B : Matrix ι ι K) (totalRows totalCols mixedRows mixedCols : Finset ι)
    (p : ℕ) (h_base_rank : A.rank ≤ p)
    (h_total : ∀ i j, i ∉ totalRows → j ∉ totalCols → (A + B) i j = 0)
    (h_mixed : ∀ i j, i ∉ mixedRows → j ∉ mixedCols → B i j = 0)
    (h_square : (A + B).mulVecLin.comp (A + B).mulVecLin = 0) :
    (A + B).rank ≤ min (totalRows.card + totalCols.card)
      (p + mixedRows.card + mixedCols.card) ∧
    Fintype.card ι - 2 * min (totalRows.card + totalCols.card)
      (p + mixedRows.card + mixedCols.card) ≤
        Module.finrank K (Smooth4Algebra.Homology (A + B).mulVecLin) := by
  have ht := rank_le_cover (A + B) totalRows totalCols h_total
  have hm := rank_le_cover B mixedRows mixedCols h_mixed
  have ha := Smooth4SupportCover.rank_add_le A B
  have hr : (A + B).rank ≤ min (totalRows.card + totalCols.card)
      (p + mixedRows.card + mixedCols.card) := by
    apply le_min ht
    omega
  have hh := homology_rank_identity (A + B) h_square
  exact ⟨hr, by omega⟩




set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SP4Table22

theorem records_size : records.size = 140 := by decide

/-- Ordinary Lean kernel computation checks every recorded support cover. -/
theorem all_certificates : ∀ k : Fin 140, Valid (record k) := by
  intro k
  fin_cases k <;> decide +kernel

end SP4Table22

theorem solution {K : Type*} [Field K] (k : Fin 140)
    (A B : Matrix (Fin 30) (Fin 30) K)
    (h_total : ∀ i j, ¬ SP4Table22.Allowed (SP4Table22.record k) i j → (A + B) i j = 0)
    (h_mixed : ∀ i j, ¬ SP4Table22.MixedAllowed (SP4Table22.record k) i j → B i j = 0)
    (h_square : (A + B).mulVecLin.comp (A + B).mulVecLin = 0) :
    (A.rank ≤ 4 → (A + B).rank ≤ 13 ∧
      4 ≤ Module.finrank K (Smooth4Algebra.Homology (A + B).mulVecLin)) ∧
    (A.rank ≤ 2 → (A + B).rank ≤ 11 ∧
      8 ≤ Module.finrank K (Smooth4Algebra.Homology (A + B).mulVecLin)) := by
  classical
  let c := SP4Table22.record k
  obtain ⟨_, ht, hm, hb4, hb2⟩ := SP4Table22.all_certificates k
  have hcover : ∀ i j, i ∉ c.totalRows.toFinset → j ∉ c.totalCols.toFinset →
      (A + B) i j = 0 := by
    intro i j hi hj
    apply h_total i j
    intro hij
    rcases ht i j hij with h | h
    · exact hi (by simpa using h)
    · exact hj (by simpa using h)
  have hmcover : ∀ i j, i ∉ c.mixedRows.toFinset → j ∉ c.mixedCols.toFinset →
      B i j = 0 := by
    intro i j hi hj
    apply h_mixed i j
    intro hij
    rcases hm i j hij with h | h
    · exact hi (by simpa using h)
    · exact hj (by simpa using h)
  constructor
  · intro ha
    obtain ⟨hr, hh⟩ := SP4Table22.support_budget A B c.totalRows.toFinset
      c.totalCols.toFinset c.mixedRows.toFinset c.mixedCols.toFinset 4 ha hcover hmcover h_square
    have hb : min (c.totalRows.toFinset.card + c.totalCols.toFinset.card)
        (4 + c.mixedRows.toFinset.card + c.mixedCols.toFinset.card) ≤ 13 := by
      simpa [SP4Table22.totalBudget, SP4Table22.mixedBudget, Nat.add_assoc, c] using hb4
    have hn : Fintype.card (Fin 30) = 30 := by simp
    exact ⟨hr.trans hb, by omega⟩
  · intro ha
    obtain ⟨hr, hh⟩ := SP4Table22.support_budget A B c.totalRows.toFinset
      c.totalCols.toFinset c.mixedRows.toFinset c.mixedCols.toFinset 2 ha hcover hmcover h_square
    have hb : min (c.totalRows.toFinset.card + c.totalCols.toFinset.card)
        (2 + c.mixedRows.toFinset.card + c.mixedCols.toFinset.card) ≤ 11 := by
      simpa [SP4Table22.totalBudget, SP4Table22.mixedBudget, Nat.add_assoc, c] using hb2
    have hn : Fintype.card (Fin 30) = 30 := by simp
    exact ⟨hr.trans hb, by omega⟩

#print axioms solution
