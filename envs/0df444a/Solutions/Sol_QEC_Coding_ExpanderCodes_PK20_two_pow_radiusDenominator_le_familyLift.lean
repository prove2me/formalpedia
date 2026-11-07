-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.two_pow_radiusDenominator_le_familyLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:22:36.984992+00:00
-- url     : https://prove2.me/submissions/fb577485-743c-40fd-b488-02b98e1a0210

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    (w radiusDenominator B : Nat) :
    2 ^ radiusDenominator ≤ familyLift w radiusDenominator B := by
  unfold familyLift
  have hTerm : 2 ^ radiusDenominator ≤
      B + 2 ^ radiusDenominator + 2 * w * radiusDenominator := by
    exact (Nat.le_add_left _ B).trans
      (Nat.le_add_right _ (2 * w * radiusDenominator))
  exact hTerm.trans
    ((Nat.le_mul_of_pos_left _ (by norm_num)).trans (Nat.le_succ _))
end QEC.Coding.ExpanderCodes.PK20
