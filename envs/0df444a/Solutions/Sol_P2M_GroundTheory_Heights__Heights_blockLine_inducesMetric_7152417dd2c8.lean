-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockLine_inducesMetric_7152417dd2c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:46.646978+00:00
-- url     : https://prove2.me/submissions/ada686be-1ff4-467c-bd48-ae702e173f29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k₀ : ι) :
    (blockAddData n k₀).InducesMetric (wholePoint n) (blockAddData n k₀).elt (blockLine n k₀).toGeo
      (blockLine (blockAddData n k₀).extSizes none).toGeo := by
  set D := blockAddData n k₀ with hD
  intro j g m dg dm _ _ _ hgm z hz
  have hz' := hz
  have hg : g = m * X ⟨k₀, j⟩ := by
    have h1 := aeval_of_hom n (ArithVariety.whole n).mkF g
    have h2 := aeval_of_hom n (ArithVariety.whole n).mkF m
    refine ArithVariety.whole_mkF_injective n ?_
    rw [map_mul, ← h1, ← h2]
    exact hgm
  have hcross : ∀ i, z ⟨none, j⟩ * z ⟨some k₀, i⟩ = z ⟨none, i⟩ * z ⟨some k₀, j⟩ := by
    intro i
    have hmem : (X (D.newCoord j) * X (D.oldCoord ⟨k₀, i⟩) - X (D.newCoord i) * X (D.oldCoord ⟨k₀, j⟩) :
        MvPolynomial (Coord D.extSizes) ℤ) ∈ Geo.mCoordIdeal (ι := blockIdx D.extSizes)
          (D.plusCoord (wholePoint n) D.elt) := by
      rw [mCoordIdeal_eq_ker, RingHom.mem_ker]
      simp only [map_sub, map_mul, eval₂Hom_X']
      have hi : D.plusCoord (wholePoint n) D.elt (D.newCoord i) =
          D.plusCoord (wholePoint n) D.elt (D.oldCoord ⟨k₀, i⟩) := rfl
      have hj : D.plusCoord (wholePoint n) D.elt (D.newCoord j) =
          D.plusCoord (wholePoint n) D.elt (D.oldCoord ⟨k₀, j⟩) := rfl
      rw [hi, hj]
      simp only [AddBlockData.newCoord, AddBlockData.oldCoord]
      ring
    have := hz.2 _ hmem
    simpa [AddBlockData.newCoord, AddBlockData.oldCoord, sub_eq_zero] using this
  have hold : BlockNonzero (unflatCone (D.oldFlat z)) := by
    refine (blockNonzero_unflatCone_iff _).mpr fun k ↦ ?_
    obtain ⟨i, hi⟩ := hz.1 (some k)
    exact ⟨i, hi⟩
  have hnew : BlockNonzero (unflatCone z) := (blockNonzero_unflatCone_iff _).mpr hz.1
  rw [HermLine.toGeo_h_of_blockNonzero _ hold, HermLine.toGeo_h_of_blockNonzero _ hnew, hg]
  change _ * _ * l2Norm (fun i ↦ z ⟨some k₀, i⟩) =
    _ * l2Norm (fun i ↦ z ⟨none, i⟩)
  have hev : eval (D.oldFlat z) (map (Int.castRingHom ℂ) (m * X ⟨k₀, j⟩)) =
      eval (D.oldFlat z) (map (Int.castRingHom ℂ) m) * z ⟨some k₀, j⟩ := by
    simp [AddBlockData.oldFlat]
  rw [hev, norm_mul]
  have key : ‖z ⟨none, j⟩‖ * l2Norm (fun i ↦ z ⟨some k₀, i⟩) =
      ‖z ⟨some k₀, j⟩‖ * l2Norm (fun i ↦ z ⟨none, i⟩) := by
    have hs : (‖z ⟨none, j⟩‖ * l2Norm (fun i ↦ z ⟨some k₀, i⟩)) ^ 2 =
        (‖z ⟨some k₀, j⟩‖ * l2Norm (fun i ↦ z ⟨none, i⟩)) ^ 2 := by
      simp only [mul_pow, l2Norm]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_pow, ← mul_pow, ← norm_mul, ← norm_mul, hcross i, mul_comm]
    exact (pow_left_inj₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) two_ne_zero).mp hs
  linear_combination ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) m)‖ * key
end GroundTheory.Heights₂.Heights
