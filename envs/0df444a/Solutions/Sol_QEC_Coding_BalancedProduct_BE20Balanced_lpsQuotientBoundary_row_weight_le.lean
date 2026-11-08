-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.lpsQuotientBoundary_row_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:55:30.363793+00:00
-- url     : https://prove2.me/submissions/842f7711-9266-4213-a765-1cdd4a592f4a

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_quotientBoundary_basis_weight_le
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_quotientBoundary_starTranspose_single
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_starTranspose_basis_weight_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (r : CheckOrbit401 q) :
    HammingWeight
      (wordLinearMapTranspose (balancingBoundary q hq40 hq)
        (Pi.single r 1)) ≤ 402 := by
  letI : Nonempty (Cyclic.CyclicGroup q) :=
    ⟨Multiplicative.ofAdd 0⟩
  unfold balancingBoundary
  rw [← quotientBoundary_starTranspose_single
    (lpsTannerGroupAlgebraMatrix q hq40 hq) r]
  apply quotientBoundary_basis_weight_le
    (LiftedProduct.starTranspose
      (lpsTannerGroupAlgebraMatrix q hq40 hq)) 402
  exact lpsTannerAction_starTranspose_basis_weight_le q hq40 hq
end QEC.Coding.BalancedProduct.BE20Balanced
