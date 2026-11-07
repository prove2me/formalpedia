-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_caseTwoRemainder_invGenerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:25:40.291089+00:00
-- url     : https://prove2.me/submissions/95bd2e86-41b5-412f-8255-c06e0f38f0f3

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_caseTwoRemainder_add_shift_eq_zero
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_caseTwoRemainder_ne_zero_of_not_boundary
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_of_invInvariant_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h) :
    q ≤ HammingWeight (caseTwoRemainder A z h) := by
  apply cyclic_card_le_HammingWeight_of_invInvariant_ne_zero q
  · exact caseTwoRemainder_add_shift_eq_zero
      A (Cyclic.cyclicGenerator q)⁻¹ z hz h hu
  · exact caseTwoRemainder_ne_zero_of_not_boundary
      A (Cyclic.cyclicGenerator q)⁻¹ z hzNotBoundary h hu
end QEC.Coding.BalancedProduct.PKDistance
