-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_boundedLocality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:02:04.843969+00:00
-- url     : https://prove2.me/submissions/db52e184-c057-497a-8a00-dd23ee9a301f

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_lpsQuotientBoundary_column_weight_le
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_lpsQuotientBoundary_row_weight_le
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_boundedLocality
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_add_ofComplexes_of_source_bounded
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_dual


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (balancedSubsystem q hq40 hq).complex).localityProfile 806 := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  have hSource : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (sourceSubsystem q hq40 hq).complex).localityProfile 404 := by
    exact lpsHorizontalSubsystem_boundedLocality q hq40 hq
  have hDual : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (sourceSubsystem q hq40 hq).dual.complex).localityProfile 404 :=
    boundedLocality_dual (sourceSubsystem q hq40 hq).complex hSource
  have hProduct := boundedLocality_add_ofComplexes_of_source_bounded
    (sourceSubsystem q hq40 hq).dual.complex
    (balancingBoundary q hq40 hq) hDual
    (lpsQuotientBoundary_row_weight_le q hq40 hq)
    (fun c => (lpsQuotientBoundary_column_weight_le q hq40 hq c).trans
      (by norm_num))
  exact hProduct
end QEC.Coding.BalancedProduct.BE20Balanced
