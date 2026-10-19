-- Prove2me | solution 1 for SoficGroups.three_pairwise_residual_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/4b382b56-f4c5-4196-8627-94605f5e8692

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_three_pair_sum_norm_sq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution
    (a b c : H) (ε : ℝ)
    (hab : (1 - ε) * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖a + b‖ ^ 2)
    (hbc : (1 - ε) * (‖b‖ ^ 2 + ‖c‖ ^ 2) ≤ ‖b + c‖ ^ 2)
    (hca : (1 - ε) * (‖c‖ ^ 2 + ‖a‖ ^ 2) ≤ ‖c + a‖ ^ 2) :
    (1 - 2 * ε) * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) ≤
      ‖a + b + c‖ ^ 2 := by
  nlinarith [three_pair_sum_norm_sq a b c]
end SoficGroups
