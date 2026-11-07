-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_nonzero_horizontalClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:33:49.107601+00:00
-- url     : https://prove2.me/submissions/e15530df-905e-48fe-b739-b0bc94ffde0a

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_horizontalAugmentation
import Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_quotientMinimumDistance_le_horizontalAugmentation


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
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    {d : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hd : 0 < d)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * d) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * d - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hzBoundary : LiftedProduct.boundary1 (Cyclic.data q A) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.data q A)).mem_middleCycleCode_iff z).1 hz
  have hAugmentation : d ≤ HammingWeight
      (HorizontalSubsystem.horizontalAugmentation z) :=
    HorizontalSubsystem.quotientMinimumDistance_le_horizontalAugmentation
      A (Cyclic.cyclicGenerator q) z hz hMinimum hProjected
  apply verticalPart_lowerBound_of_horizontalAugmentation
    q A z hzBoundary (q * d) stepBound expansionNumerator
      expansionDenominator
  · exact Nat.mul_pos hq hd
  · exact Nat.mul_le_mul_left q hAugmentation
  · exact hstepBound
  · exact hExpansion
end QEC.Coding.BalancedProduct.PKDistance
