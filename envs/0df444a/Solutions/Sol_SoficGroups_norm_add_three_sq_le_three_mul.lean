-- Prove2me | solution 1 for SoficGroups.norm_add_three_sq_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/26e28c42-7f03-4624-9153-5bdbb387f4a0

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
omit [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution (a b c : H) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have htriangle : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    calc
      ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by gcongr; exact norm_add_le a b
  have hsquare :
      ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  nlinarith [sq_nonneg (‖a‖ - ‖b‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖c‖ - ‖a‖)]
end SoficGroups
