-- Prove2me | solution 1 for PI.WGB.stepA_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:16:50.121103+00:00
-- url     : https://prove2.me/submissions/e4dd51eb-b89f-4d17-9f24-315310da87f5

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_PI_WGB_mrow_invA
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mcol_inv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (stepA p q x) = φ x := by
  unfold stepA
  simp only
  rw [lhwline_mcol_inv φ hC _ _ _ _ (fun j hj => (Finset.mem_filter.mp hj).2),
    mrow_invA φ hR _ _ _ _ (fun b hb => (Finset.mem_filter.mp hb).2)]
end PI.WGB
