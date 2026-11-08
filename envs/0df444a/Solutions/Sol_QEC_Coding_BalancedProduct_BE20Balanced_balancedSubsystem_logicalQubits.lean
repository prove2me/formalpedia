-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_logicalQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:53:55.516912+00:00
-- url     : https://prove2.me/submissions/6e263638-74bc-4806-9f82-35c02ed62907

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_balancedKernelSubsystemData_logicalQubits
import Theorems.Thm_QEC_Coding_SubsystemCSSData_dual_logicalQubits
attribute [local simp] QEC.Coding.SubsystemCSSData.dual_logicalQubits



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    (balancedSubsystem q hq40 hq).logicalQubits =
      (sourceSubsystem q hq40 hq).logicalQubits *
        Module.finrank (ZMod 2)
          (LinearMap.ker (balancingBoundary q hq40 hq)) := by
  letI : Nonempty (EdgeOrbit401 q hq) :=
    edgeOrbit401Nonempty q hq40 hq
  rw [balancedSubsystem, balancedKernelSubsystemData_logicalQubits,
    SubsystemCSSData.dual_logicalQubits]
  change (sourceSubsystem q hq40 hq).logicalQubits *
      Module.finrank (ZMod 2)
        (LinearMap.ker (Matrix.toLin'
          (LinearMap.toMatrix' (balancingBoundary q hq40 hq)))) = _
  rw [Matrix.toLin'_toMatrix']
end QEC.Coding.BalancedProduct.BE20Balanced
