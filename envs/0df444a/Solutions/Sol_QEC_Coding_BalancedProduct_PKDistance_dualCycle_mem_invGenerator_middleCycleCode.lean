-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.dualCycle_mem_invGenerator_middleCycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:00:43.401129+00:00
-- url     : https://prove2.me/submissions/a128da2f-49a3-474c-ac04-78b92045ab04

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_cyclicLiftedProductData
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_mem_middleCycleCode_of_mem_middleCocycleCode


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
      (Cyclic.data q A)).middleCocycleCode.carrier) :
    LiftedProductDuality.swapWord z ∈
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier := by
  have hDual :=
    LiftedProductDuality.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
      (Cyclic.data q A) z hz
  change LiftedProductDuality.swapWord z ∈
    (LiftedProduct.chainComplex
      (LiftedProductDuality.dualData
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)))).middleCycleCode.carrier at hDual
  rw [LiftedProductDuality.dualData_cyclicLiftedProductData] at hDual
  exact hDual
end QEC.Coding.BalancedProduct.PKDistance
