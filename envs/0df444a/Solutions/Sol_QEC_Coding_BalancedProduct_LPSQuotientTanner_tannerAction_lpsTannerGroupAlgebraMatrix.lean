-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerAction_lpsTannerGroupAlgebraMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:46:43.482253+00:00
-- url     : https://prove2.me/submissions/708600fa-940f-4a4e-be4d-28522b6b0cea

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerCoefficient_smul
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerBoundary_eq_sum_tannerCoefficient
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_sum_rightRegularMatrix_groupAlgebraMatrix


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance
namespace QEC.Coding.BalancedProduct.LPSQuotientTanner
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)
        (edgeWordInOrbitCoordinates q hq x) =
      checkWordInOrbitCoordinates q (tannerBoundary q hq40 hq x) := by
  funext p
  rcases p with ⟨ro, go⟩
  rw [tannerAction_apply]
  change
    (∑ co : EdgeOrbit401 q hq, ∑ gi : CyclicGroup q,
      LiftedProduct.rightRegularMatrix
          (lpsTannerGroupAlgebraMatrix q hq40 hq ro co) go gi *
        x ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, gi))) =
      tannerBoundary q hq40 hq x
        ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, go))
  rw [tannerBoundary_eq_sum_tannerCoefficient]
  exact sum_rightRegularMatrix_groupAlgebraMatrix
    (CyclicGroup q) (tannerCoefficient q hq40 hq)
    (tannerCoefficient_smul q hq40 hq) x ro go
end QEC.Coding.BalancedProduct.LPSQuotientTanner
