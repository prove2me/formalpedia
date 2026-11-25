-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_volume_linProj_image_null_7ac35fee0eee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:24.1618+00:00
-- url     : https://prove2.me/submissions/454b8aeb-f25c-4471-98da-a673395c170f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeAreaFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_null_of_hausdorff_null_a26ea8030678

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
open MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m n : ℕ} (π : Fin m → Fin n → ℂ) {s : Set (EuclideanSpace ℂ (Fin n))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume (linProj π '' s) = 0 := by
  refine volume_null_of_hausdorff_null (nonpos_iff_eq_zero.1 ?_)
  have hL := (LinearMap.toContinuousLinearMap (linProjₗ π)).lipschitz.hausdorffMeasure_image_le
    (d := ((2 * m : ℕ) : ℝ)) (by positivity) s
  rw [LinearMap.coe_toContinuousLinearMap', hs, mul_zero] at hL
  exact hL
end GroundTheory.Heights₂.Heights
