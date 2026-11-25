-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_scale_b69d59385d69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:26.222994+00:00
-- url     : https://prove2.me/submissions/8e26ac84-25ee-462f-bdcd-93ecb70ce056

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca

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
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric
namespace GroundTheory.Heights₂.Heights.ChartMetric
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ) (d : ι → ℕ) :
    ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (fun k i ↦ t k * z k i) (chartMonomial c d)‖ ^ 2 =
      (∏ k, ‖t k‖ ^ (2 * (d k : ℤ))) * ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦
    norm_sq_evalCone_scale t z (isWeightedHomogeneous_chartMonomial c d)
end GroundTheory.Heights₂.Heights.ChartMetric
