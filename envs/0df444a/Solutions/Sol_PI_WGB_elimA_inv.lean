-- Prove2me | solution 1 for PI.WGB.elimA_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:40.753847+00:00
-- url     : https://prove2.me/submissions/b3943f00-a455-444d-b113-aec1e715ac2b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_PI_WGB_stepA_inv
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
    (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (elimA k x) = φ x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [elimA]
    split_ifs
    · rw [stepA_inv φ hR hC, ih]
    · exact ih
end PI.WGB
