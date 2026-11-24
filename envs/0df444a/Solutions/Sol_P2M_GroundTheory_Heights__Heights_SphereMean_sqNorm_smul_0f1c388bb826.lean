-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:54.0518+00:00
-- url     : https://prove2.me/submissions/f43fd434-f8d0-453f-af02-b91b2fcacd59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol

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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]
end GroundTheory.Heights₂.Heights.SphereMean
