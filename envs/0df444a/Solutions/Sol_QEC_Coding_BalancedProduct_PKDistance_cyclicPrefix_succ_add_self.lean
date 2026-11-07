-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_succ_add_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:08.545612+00:00
-- url     : https://prove2.me/submissions/f12e6e8a-810a-40a6-ad9c-fff888e808ea

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_succ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x (t + 1) z + cyclicPrefix x t z =
      cyclicShift (x ^ t) z := by
  rw [cyclicPrefix_succ, add_assoc,
    add_comm (cyclicShift (x ^ t) z) (cyclicPrefix x t z),
    ← add_assoc, binaryWord_add_self, zero_add]
end QEC.Coding.BalancedProduct.PKDistance
