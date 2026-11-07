-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicPrefix_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:29.125507+00:00
-- url     : https://prove2.me/submissions/792b7b5f-ef71-463b-a62b-54d2410bc044

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicShift
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_succ_add_self

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    HammingWeight (cyclicPrefix x (t + 1) z + cyclicPrefix x t z) =
      HammingWeight z := by
  rw [cyclicPrefix_succ_add_self, HammingWeight_cyclicShift]
end QEC.Coding.BalancedProduct.PKDistance
