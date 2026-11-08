-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_dressedDistanceBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:36:23.431941+00:00
-- url     : https://prove2.me/submissions/cc4d6058-d29b-4ecf-be2b-56da2bb291b3

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancingBoundary_classicalDistanceAtLeast
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_dressedDistanceBounds
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_balancedKernelSubsystemData_dressedXDistanceAtLeast
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
import Theorems.Thm_QEC_Coding_SubsystemCSSData_dual_dressedXDistanceAtLeast_iff
import Theorems.Thm_QEC_Coding_SubsystemCSSData_dual_dressedZDistanceAtLeast_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq804 : 804 ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq))
    (hCheckOrbitLarge : 10000000 ≤ Fintype.card (CheckOrbit401 q)) :
    (balancedSubsystem q hq40 hq).DressedXDistanceAtLeast
        (lpsDressedZLowerBound q hq) ∧
      (balancedSubsystem q hq40 hq).DressedZDistanceAtLeast
        ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
          lpsDressedXLowerBound q) := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  have hSource := lpsHorizontalSubsystem_dressedDistanceBounds
    q hq40 hq804 hq hLPS hEdgeOrbitLarge hCheckOrbitLarge
  have hDualZ : (sourceSubsystem q hq40 hq).dual.DressedZDistanceAtLeast
      (lpsDressedXLowerBound q) :=
    ((sourceSubsystem q hq40 hq).dual_dressedZDistanceAtLeast_iff _).2 hSource.2
  have hDualX : (sourceSubsystem q hq40 hq).dual.DressedXDistanceAtLeast
      (lpsDressedZLowerBound q hq) :=
    ((sourceSubsystem q hq40 hq).dual_dressedXDistanceAtLeast_iff _).2 hSource.1
  constructor
  · exact balancedKernelSubsystemData_dressedXDistanceAtLeast
      (sourceSubsystem q hq40 hq).dual (balancingBoundary q hq40 hq) hDualX
  · exact balancedKernelSubsystemData_dressedZDistanceAtLeast_mul
      (sourceSubsystem q hq40 hq).dual (balancingBoundary q hq40 hq)
      hDualZ (balancingBoundary_classicalDistanceAtLeast q hq40 hq hLPS)
end QEC.Coding.BalancedProduct.BE20Balanced
