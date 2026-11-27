-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegConeLimit_proof_54f0ee3ca621
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:50.032572+00:00
-- url     : https://prove2.me/submissions/1679aae5-07b3-4383-b7ed-7603fe104c83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegConeLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegConeLimit_abs_fsLogReg_pointOf_le_cc18305be98c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegConeLimit_measurable_fsLogReg_pointOf_9f16abb635bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e


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
open MvPolynomial MeasureTheory Filter Topology Set ConeFsLog
noncomputable section
open RegConeLimit
namespace GroundTheory.Heights₂.Heights
namespace RegConeLimit
theorem _root_.solution (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : RegConeLimit.Statement := by
  intro n e h J u hJ ⟨f, hf⟩ hu
  set μ : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
    with hμ
  have : IsFiniteMeasure (μ.restrict (coneBall h J)) :=
    isFiniteMeasure_restrict.mpr (hFin n e h J f hJ hf).ne
  set K := Real.log (h.norm u ^ 2 + 1) / 2

  have hS : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ∑ j, u j * h.pointOf y j = 0} := by
    have hp : Continuous fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y := by
      unfold HermNorm.pointOf
      fun_prop
    exact (isClosed_eq (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)) continuous_const).measurableSet
  have hae : ∀ᵐ y ∂(μ.restrict (coneBall h J)), ∑ j, u j * h.pointOf y j ≠ 0 := by
    have h0 : μ.restrict (coneBall h J) {y | ∑ j, u j * h.pointOf y j = 0} = 0 := by
      rw [Measure.restrict_apply hS, inter_comm]
      exact hNull n e h J f u hJ hf hu
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with y hy
    exact hy
  have hlim : Tendsto (fun ε => ∫ y in coneBall h J, fsLogReg h u ε (h.pointOf y) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ y in coneBall h J, fsLog h u (h.pointOf y) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => |fsLog h u (h.pointOf y)| + K) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε => (measurable_fsLogReg_pointOf h u ε).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      filter_upwards [hae] with y hy
      rw [Real.norm_eq_abs]
      exact abs_fsLogReg_pointOf_le h u y hε.1 hε.2.le hy
    · exact (hInt n e h J f u hJ hf hu).abs.add (integrable_const K)
    · filter_upwards [hae] with y hy
      have hy0 : 0 < h.dualNorm (h.pointOf y) := by
        rw [dualNorm_pointOf]
        rcases (norm_nonneg y).eq_or_lt with h0 | h0
        · have := norm_sum_mul_pointOf_le h u y
          rw [← h0, mul_zero] at this
          exact absurd (norm_le_zero_iff.mp this) hy
        · exact h0
      exact (fsLogReg_tendsto h u (h.pointOf y) hy0 hy).mono_left nhdsWithin_le_nhds
  exact hlim.div_const _
end RegConeLimit
end GroundTheory.Heights₂.Heights
