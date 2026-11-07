-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.HammingWeight_tannerAction_cyclicDifference_le_two_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:25:39.29547+00:00
-- url     : https://prove2.me/submissions/f8e4ae95-3a91-42f7-96d9-abc5f99d5239

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_add_cyclicShift_le_two_mul
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_tannerAction_cyclicDifference_eq_verticalDifference_caseTwo

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {G aRow aCol : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit G))
    (hz : LiftedProduct.boundary1 (Cyclic.liftedProductData A x) z = 0)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h)
    (t : Nat) :
    HammingWeight (tannerAction A (h + cyclicShift (x ^ t) h)) ≤
        2 * HammingWeight (verticalPart z) := by
  rw [tannerAction_cyclicDifference_eq_verticalDifference_caseTwo
    A x z hz h hu t]
  exact HammingWeight_add_cyclicShift_le_two_mul (x ^ t) (verticalPart z)
end QEC.Coding.BalancedProduct.PKDistance
