-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.rightRegular_lpsTannerGroupAlgebraMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:54:47.670738+00:00
-- url     : https://prove2.me/submissions/29c7377a-2d8c-4809-880d-a4a6b333f368

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerCoefficient_smul
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_rightRegularMatrix_groupAlgebraMatrix


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
    (ro : CheckOrbit401 q) (co : EdgeOrbit401 q hq)
    (go gi : CyclicGroup q) :
    LiftedProduct.rightRegularMatrix
        (lpsTannerGroupAlgebraMatrix q hq40 hq ro co) go gi =
      tannerCoefficient q hq40 hq
        ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, go))
        ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, gi)) := by
  exact rightRegularMatrix_groupAlgebraMatrix
    (CyclicGroup q) (tannerCoefficient q hq40 hq)
    (tannerCoefficient_smul q hq40 hq) ro co go gi
end QEC.Coding.BalancedProduct.LPSQuotientTanner
