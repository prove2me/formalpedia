-- Prove2me | solution 1 for SNumbers.detNumber_succ_le_hilbertNumber_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:44:10.818425+00:00
-- url     : https://prove2.me/submissions/dbe824a6-5872-4c8d-a4a7-0e68c80b933e

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_detSet_nonempty
public import Theorems.Thm_SNumbers_detNumber_nonneg
public import Theorems.Thm_SNumbers_prod_approximationNumber_le_detNumber
public import Theorems.Thm_SNumbers_approximationNumber_eucl_comp_comp_le_mul_hilbertNumber
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_SNumbers_prod_approximationNumber_eq_norm_det


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    detNumber S (n + 1) ≤ hilbertNumber S n * detNumber S n := by
  refine csSup_le (detSet_nonempty S (n + 1)) ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  have : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have h1 : ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖
      = ∏ i ∈ Finset.range (n + 1), approximationNumber (B.comp (S.comp A)) i := by
    have h := prod_approximationNumber_eq_norm_det (B.comp (S.comp A))
    rw [finrank_euclideanSpace_fin] at h
    exact h.symm
  have h2 : ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := prod_approximationNumber_le_detNumber S hA hB
  have h3 : approximationNumber (B.comp (S.comp A)) n ≤ hilbertNumber S n := by
    have h := approximationNumber_eucl_comp_comp_le_mul_hilbertNumber S n n A B
    calc approximationNumber (B.comp (S.comp A)) n
        ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := h
      _ ≤ 1 * hilbertNumber S n :=
          mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (norm_nonneg _) hB).trans hA)
            (hilbertNumber_nonneg S n)
      _ = hilbertNumber S n := one_mul _
  rw [h1, Finset.prod_range_succ]
  calc (∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i) *
        approximationNumber (B.comp (S.comp A)) n
      ≤ detNumber S n * hilbertNumber S n :=
        mul_le_mul h2 h3 (approximationNumber_nonneg _ _) (detNumber_nonneg S n)
    _ = hilbertNumber S n * detNumber S n := mul_comm _ _
end SNumbers
