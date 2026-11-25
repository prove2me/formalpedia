-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_scale_alg_9e8d282e6431
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:47.66521+00:00
-- url     : https://prove2.me/submissions/ed42da71-45a9-4671-88af-f85797031e53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale

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
theorem _root_.solution (A B h s L S Den : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < Den) :
    A * h * (s * L) * Real.sqrt (B * S / (B * A ^ 2 * Den)) = s * (h * L * Real.sqrt (S / Den)) := by
  have e : B * S / (B * A ^ 2 * Den) = S / Den / A ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div' _ (sq_nonneg A), Real.sqrt_sq hA.le]
  field_simp
end GroundTheory.Heights₂.Heights.ChartMetric
