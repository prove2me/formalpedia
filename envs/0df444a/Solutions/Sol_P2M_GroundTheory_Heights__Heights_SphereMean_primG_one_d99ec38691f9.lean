-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_primG_one_d99ec38691f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:26.257802+00:00
-- url     : https://prove2.me/submissions/ae757785-2cf0-4161-aea6-b067b0fa9d6c

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
theorem _root_.solution (m : ℕ) : primG m 1 = -(harmonic (m + 1) : ℝ) / (m + 1) := by
  simp only [primG, polyR, sub_self, log_one, mul_zero, zero_sub, ne_eq, add_eq_zero,
    one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  rw [harmonic]
  push_cast
  rw [neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp
end GroundTheory.Heights₂.Heights.SphereMean
