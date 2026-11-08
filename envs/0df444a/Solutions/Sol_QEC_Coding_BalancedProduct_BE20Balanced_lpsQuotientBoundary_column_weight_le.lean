-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.lpsQuotientBoundary_column_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:48:18.32407+00:00
-- url     : https://prove2.me/submissions/89fba10e-0874-4570-9e8f-0faf0950401f

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_quotientBoundary_basis_weight_le
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_basis_weight_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (c : EdgeOrbit401 q hq) :
    HammingWeight (balancingBoundary q hq40 hq (Pi.single c 1)) ≤ 400 := by
  letI : Nonempty (Cyclic.CyclicGroup q) :=
    ⟨Multiplicative.ofAdd 0⟩
  apply quotientBoundary_basis_weight_le
    (lpsTannerGroupAlgebraMatrix q hq40 hq) 400
  exact lpsTannerAction_basis_weight_le q hq40 hq
end QEC.Coding.BalancedProduct.BE20Balanced
