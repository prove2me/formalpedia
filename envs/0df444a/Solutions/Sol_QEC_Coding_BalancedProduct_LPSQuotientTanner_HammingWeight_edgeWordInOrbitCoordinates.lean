-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.HammingWeight_edgeWordInOrbitCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:32:24.653493+00:00
-- url     : https://prove2.me/submissions/155e799f-550d-4fad-8361-79b47535db0f

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_precomp_equiv


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
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    HammingWeight (edgeWordInOrbitCoordinates q hq x) = HammingWeight x := by
  exact HammingWeight_precomp_equiv
    (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm x
end QEC.Coding.BalancedProduct.LPSQuotientTanner
