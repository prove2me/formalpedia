-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.dualCycle_not_boundary_of_horizontalCohomologyProjection_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:55.191992+00:00
-- url     : https://prove2.me/submissions/035f9532-b673-4959-966c-782ec3697d47

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode


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
        (LiftedProductDuality.dualData
          (Cyclic.data q A))).middleBoundaryCode.carrier := by
  intro hBoundary
  have hCoboundary : z ∈
      (LiftedProduct.chainComplex
        (Cyclic.data q A)).firstCoboundaryCheckCode.carrier :=
    LiftedProductDuality.mem_firstCoboundaryCheckCode_of_swapWord_mem_middleBoundaryCode
      (Cyclic.data q A) z hBoundary
  apply hProjected
  have hClassZero :
      (LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩ = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      (LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles).2
    exact hCoboundary
  rw [hClassZero]
  exact (HorizontalSubsystem.horizontalCohomologyProjection A
    (Cyclic.cyclicGenerator q)).map_zero
end QEC.Coding.BalancedProduct.PKDistance
