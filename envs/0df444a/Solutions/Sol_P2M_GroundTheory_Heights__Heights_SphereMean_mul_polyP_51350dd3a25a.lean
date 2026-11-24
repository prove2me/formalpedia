-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_mul_polyP_51350dd3a25a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.799786+00:00
-- url     : https://prove2.me/submissions/8796c013-ad92-400b-8a62-4a34ddaaa714

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc

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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) (s : ℝ) : s * polyP m s = (1 - (1 - s) ^ (m + 1)) / (m + 1) := by
  have h := geom_sum_mul (1 - s) (m + 1)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold polyP
  rw [← Finset.sum_div, eq_div_iff hm, mul_div_assoc', div_mul_cancel₀ _ hm]
  linear_combination (-1 : ℝ) * h
end GroundTheory.Heights₂.Heights.SphereMean
