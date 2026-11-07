-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.familyLift_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:22:32.466762+00:00
-- url     : https://prove2.me/submissions/5661c26e-e288-4d04-afcf-ebd07410459b

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution (w radiusDenominator B : Nat) :
    B < familyLift w radiusDenominator B := by
  unfold familyLift
  have hB : B ≤ B + 2 ^ radiusDenominator + 2 * w * radiusDenominator := by
    exact (Nat.le_add_right B (2 ^ radiusDenominator)).trans
      (Nat.le_add_right _ (2 * w * radiusDenominator))
  have hDouble : B + 2 ^ radiusDenominator + 2 * w * radiusDenominator ≤
      2 * (B + 2 ^ radiusDenominator + 2 * w * radiusDenominator) := by
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  exact lt_of_le_of_lt (hB.trans hDouble) (Nat.lt_succ_self _)
end QEC.Coding.ExpanderCodes.PK20
