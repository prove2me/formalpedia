-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_polyR_1a5b2ce114a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:00.051212+00:00
-- url     : https://prove2.me/submissions/c0b63ec9-5c4b-4da8-bb90-86a61218c7b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_one_sub_pow_438a1539a70c

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
theorem _root_.solution (m : ℕ) (s : ℝ) : HasDerivAt (polyR m) (polyP m s) s := by
  unfold polyR polyP
  apply HasDerivAt.fun_sum
  intro j _
  have h2 := ((hasDerivAt_one_sub_pow (j + 1) s).const_sub 1).div_const (((j : ℝ) + 1) * (m + 1))
  refine h2.congr_deriv ?_
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, neg_neg]
  push_cast
  field_simp
end GroundTheory.Heights₂.Heights.SphereMean
