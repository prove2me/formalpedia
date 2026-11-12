-- Prove2me | solution 1 for ProxGapTight.thresholds_ordered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:08.594426+00:00
-- url     : https://prove2.me/submissions/36e5914a-4ed6-4a35-bdab-9d3baaf0efdf

import Mathlib
import Definitions.Def_ProxGapTight_J32
import Definitions.Def_ProxGapTight_Gam

section
set_option autoImplicit false

namespace ProxGapTight

theorem chk_thresholds_ordered (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    J32 δ < Gam δ ∧ Gam δ < δ := by
  have ha0 : 0 < 1 - δ := by linarith
  have ha1 : 1 - δ < 1 := by linarith
  constructor
  · unfold J32 Gam
    have := Real.rpow_lt_rpow_of_exponent_gt ha0 ha1 (show (1:ℝ)/3 < 4/9 by norm_num)
    linarith
  · unfold Gam
    have := Real.rpow_lt_rpow_of_exponent_gt ha0 ha1 (show (4:ℝ)/9 < 1 by norm_num)
    rw [Real.rpow_one] at this
    linarith

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_thresholds_ordered := @ProxGapTight.chk_thresholds_ordered
