-- Prove2me | solution 1 for Smooth4Algebra.support_cover_homology_budget
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T02:00:15.500698+00:00
-- url     : https://prove2.me/submissions/9ea2dd5d-7d67-41fc-bb5f-bd2fcd2bb204

import Mathlib
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
theorem solution {K ι : Type*} [Field K] [Fintype ι]
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


#print axioms solution
