-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.exists_normalized_horizontalPrimitive_of_homologyProjection_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:23.612113+00:00
-- url     : https://prove2.me/submissions/6342903e-6488-4b3d-aec6-973e5faf0ba5

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_cyclicPrimitive
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_fibreSum_horizontalPart_eq_horizontalAugmentation
import Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0) :
    ∃ h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q),
      horizontalPart z =
        h + cyclicShift (Cyclic.cyclicGenerator q) h ∧
      ∀ c, 2 * fibreWeight h c ≤ q := by
  have hAugmentation : HorizontalSubsystem.horizontalAugmentation z = 0 :=
    HorizontalSubsystem.horizontalAugmentation_eq_zero_of_homologyProjection_eq_zero
      A (Cyclic.cyclicGenerator q) z hz hProjected
  apply exists_normalized_cyclicPrimitive q hq (horizontalPart z)
  rw [fibreSum_horizontalPart_eq_horizontalAugmentation]
  exact hAugmentation
end QEC.Coding.BalancedProduct.PKDistance
