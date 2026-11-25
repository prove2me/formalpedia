-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integral_disc_weight_9841087968d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:15.910899+00:00
-- url     : https://prove2.me/submissions/379e8d13-1ab6-4989-9066-9283a11c25e4

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
theorem _root_.solution (m : ℕ) :
    ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ m = 1 / (2 * ((m : ℝ) + 1)) := by
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1)))
      (y * (1 - y ^ 2) ^ m) y := by
    intro y _
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have := (HasDerivAt.comp (h := fun x : ℝ => x ^ 2) y (hasDerivAt_one_sub_pow (m + 1) (y ^ 2))
      hp).neg.div_const (2 * ((m : ℝ) + 1))
    have h3 : HasDerivAt (fun y : ℝ => -(1 - y ^ 2) ^ (m + 1) / (2 * (m + 1)))
        (-(-((((m + 1 : ℕ) : ℝ)) * (1 - y ^ 2) ^ (m + 1 - 1)) * (2 * y)) / (2 * ((m : ℝ) + 1))) y :=
      this
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun y => y * (1 - y ^ 2) ^ m) hd
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  field_simp
  simp
end GroundTheory.Heights₂.Heights.SphereMean
