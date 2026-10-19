-- Prove2me | solution 1 for SoficGroups.three_pair_sum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/5700b483-9d45-4549-b13e-308e59859f96

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution (a b c : H) :
    ‖a + b‖ ^ 2 + ‖b + c‖ ^ 2 + ‖c + a‖ ^ 2 =
      ‖a + b + c‖ ^ 2 + (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hca :
      RCLike.re (inner ℂ c a) = RCLike.re (inner ℂ a c) := by
    exact @inner_re_symm ℂ H _ _ _ c a
  simp only [@norm_add_sq ℂ H, inner_add_left, map_add]
  nlinarith
end SoficGroups
