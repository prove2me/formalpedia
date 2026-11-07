-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.normalizeCyclicFibres_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:16:03.857353+00:00
-- url     : https://prove2.me/submissions/bfcd5a8a-7e24-4871-8edf-8a45299db04c

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_normalizeBinaryWord_le_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) (i : I) :
    2 * HammingWeight (fun g : G => normalizeCyclicFibres z (i, g)) ≤
      Fintype.card G := by
  exact FiberBundle.twice_hammingWeight_normalizeBinaryWord_le_card
    (fun g : G => z (i, g))
end QEC.Coding.BalancedProduct.PKDistance
