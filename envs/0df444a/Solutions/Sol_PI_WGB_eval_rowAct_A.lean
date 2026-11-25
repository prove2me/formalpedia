-- Prove2me | solution 1 for PI.WGB.eval_rowAct_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:18.975701+00:00
-- url     : https://prove2.me/submissions/81c9403f-f643-4b23-9180-02cce2e75925

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution {r c : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (x : Fin r × Fin c → ℂ)
    (f : MvPolynomial (Fin r × Fin c) ℂ) :
    eval x (rowAct ℂ M f) = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) f := by
  have h : (eval x).comp (rowAct ℂ (n := c) M).toRingHom = eval (fun v => ∑ b, M v.1 b * x (b, v.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) h
end PI.WGB
