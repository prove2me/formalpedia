-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.dualCycle_not_invGenerator_boundary_of_horizontalCohomologyProjection_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:25:50.552598+00:00
-- url     : https://prove2.me/submissions/035fda96-ac27-4b2b-9121-701f17352980

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_cyclicLiftedProductData


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
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0) :
    LiftedProductDuality.swapWord z ∉
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData (LiftedProduct.starTranspose A)
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier := by
  have hDual := dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
    q A z hz hProjected
  change LiftedProductDuality.swapWord z ∉
    (LiftedProduct.chainComplex
      (LiftedProductDuality.dualData
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)))).middleBoundaryCode.carrier at hDual
  rw [LiftedProductDuality.dualData_cyclicLiftedProductData] at hDual
  exact hDual
end QEC.Coding.BalancedProduct.PKDistance
