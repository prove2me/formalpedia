-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.eq_cyclicShift_of_add_shift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:02:27.583246+00:00
-- url     : https://prove2.me/submissions/b13efd1d-ba07-4784-9250-2cf2022c285b

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G))
    (hzero : z + cyclicShift x z = 0) :
    z = cyclicShift x z := by
  have hself := binaryWord_add_self (cyclicShift x z)
  calc
    z = z + 0 := by rw [add_zero]
    _ = z + (cyclicShift x z + cyclicShift x z) := by rw [hself]
    _ = (z + cyclicShift x z) + cyclicShift x z := by rw [add_assoc]
    _ = cyclicShift x z := by rw [hzero, zero_add]
end QEC.Coding.BalancedProduct.PKDistance
