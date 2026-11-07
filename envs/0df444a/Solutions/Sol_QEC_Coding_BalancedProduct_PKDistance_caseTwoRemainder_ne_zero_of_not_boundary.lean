-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.caseTwoRemainder_ne_zero_of_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:49.992198+00:00
-- url     : https://prove2.me/submissions/8137a581-87a7-4eb5-869b-6dabe8996fbe

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryWord_add_self
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_boundary2_primitiveTwoChain
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_boundary2_primitiveTwoChain

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
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).middleBoundaryCode.carrier)
    (h : Word (ZMod 2) (aCol × G))
    (hu : horizontalPart z = h + cyclicShift x h) :
    caseTwoRemainder A z h ≠ 0 := by
  intro hzero
  change verticalPart z + tannerAction A h = 0 at hzero
  have hv : verticalPart z = tannerAction A h := by
    have hself := binaryWord_add_self (tannerAction A h)
    calc
      verticalPart z = verticalPart z + 0 := by rw [add_zero]
      _ = verticalPart z + (tannerAction A h + tannerAction A h) := by
        rw [hself]
      _ = (verticalPart z + tannerAction A h) + tannerAction A h := by
        rw [add_assoc]
      _ = tannerAction A h := by rw [hzero, zero_add]
  apply hzNotBoundary
  apply ((LiftedProduct.chainComplex
    (Cyclic.liftedProductData A x)).mem_middleBoundaryCode_iff z).2
  refine ⟨primitiveTwoChain h, ?_⟩
  funext q
  cases q with
  | inl p =>
      rcases p with ⟨c, u, g⟩
      cases u
      have hblock := congrFun
        (horizontalPart_boundary2_primitiveTwoChain A x h) (c, g)
      have hu' := congrFun hu (c, g)
      exact hblock.trans hu'.symm
  | inr p =>
      rcases p with ⟨r, u, g⟩
      cases u
      have hblock := congrFun
        (verticalPart_boundary2_primitiveTwoChain A x h) (r, g)
      have hv' := congrFun hv (r, g)
      exact hblock.trans hv'.symm
end QEC.Coding.BalancedProduct.PKDistance
