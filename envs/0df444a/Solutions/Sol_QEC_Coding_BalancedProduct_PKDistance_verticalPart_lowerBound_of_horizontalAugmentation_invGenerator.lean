-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_horizontalAugmentation_invGenerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:29:37.583202+00:00
-- url     : https://prove2.me/submissions/0952195e-9c3e-4482-a1f1-ded61332de33

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_cyclicPrefix_crossing
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_invCyclicPrefix_card
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_fibreSum_horizontalPart_eq_horizontalAugmentation

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
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0)
    (threshold stepBound expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (haugmentation : threshold ≤ q * HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z))
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      threshold expansionNumerator expansionDenominator) :
    expansionNumerator * (threshold - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  apply verticalPart_lowerBound_of_cyclicPrefix_crossing
    A (Cyclic.cyclicGenerator q)⁻¹ z hz q threshold stepBound
      expansionNumerator expansionDenominator hthreshold
  · rw [HammingWeight_invCyclicPrefix_card,
      fibreSum_horizontalPart_eq_horizontalAugmentation]
    exact haugmentation
  · exact hstepBound
  · exact hExpansion
end QEC.Coding.BalancedProduct.PKDistance
