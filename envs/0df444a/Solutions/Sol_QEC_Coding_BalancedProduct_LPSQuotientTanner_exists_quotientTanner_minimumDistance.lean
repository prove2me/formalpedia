-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.exists_quotientTanner_minimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:50:19.246738+00:00
-- url     : https://prove2.me/submissions/56ca2ef8-be1a-49a0-9068-eedc511d1863

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_quotientTanner_middleCycleCode_exists_nonzero
import Theorems.Thm_QEC_Coding_exists_minimumDistance_of_exists_nonzero


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
    (hq : legendreSym q 401 = -1) :
    ∃ d : ℕ, MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode d := by
  apply exists_minimumDistance_of_exists_nonzero
  exact quotientTanner_middleCycleCode_exists_nonzero q hq40 hq
end QEC.Coding.BalancedProduct.LPSQuotientTanner
