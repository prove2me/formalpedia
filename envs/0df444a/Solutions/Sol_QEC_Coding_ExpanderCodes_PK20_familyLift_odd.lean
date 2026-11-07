-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.familyLift_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:22:31.425123+00:00
-- url     : https://prove2.me/submissions/a811f911-895a-4882-ac47-72eaaf995f9e

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
    Odd (familyLift w radiusDenominator B) := by
  exact odd_two_mul_add_one _
end QEC.Coding.ExpanderCodes.PK20
