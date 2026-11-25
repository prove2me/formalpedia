-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_homogenize_c2c6fe846b43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:45.716964+00:00
-- url     : https://prove2.me/submissions/53b98d7c-50b4-4a94-aff4-46d4c5973aa7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_smul_of_isHomogeneous_b53e6725adc1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.GoodChartZeroSet
namespace GroundTheory.Heights₂.Heights.GoodChartZeroSet
theorem _root_.solution {m : ℕ} (f : MvPolynomial (Fin m) ℂ) {D : ℕ} (hD : f.totalDegree ≤ D) (a : Fin m)
    (w : Fin m → ℂ) (hw : w a ≠ 0) :
    eval w (X a * ∑ d ∈ range (D + 1), X a ^ (D - d) * homogeneousComponent d f) =
      w a ^ (D + 1) * eval ((w a)⁻¹ • w) f := by
  have hf : f = ∑ d ∈ range (D + 1), homogeneousComponent d f := by
    conv_lhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun d _ hd' => ?_
    exact homogeneousComponent_eq_zero (n := d) (φ := f) (by simp at hd'; omega)
  conv_rhs => rw [hf]
  rw [map_mul, map_sum, map_sum, eval_X, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : d ≤ D := by simp at hd; omega
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d f), map_mul, map_pow, eval_X]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdD
  rw [Nat.add_sub_cancel_left]
  have hinv : w a ^ d * (w a)⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  linear_combination (-(w a * w a ^ k * eval w (homogeneousComponent d f))) * hinv
end GroundTheory.Heights₂.Heights.GoodChartZeroSet
