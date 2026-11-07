-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_cyclicDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:56.072957+00:00
-- url     : https://prove2.me/submissions/24d69f73-22af-447e-9b47-4b2cc87dde61

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_add_shift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_add
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_cyclicShift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t (z + cyclicShift x z) =
      z + cyclicShift (x ^ t) z := by
  rw [cyclicPrefix_add, cyclicPrefix_cyclicShift,
    cyclicPrefix_add_shift]
end QEC.Coding.BalancedProduct.PKDistance
