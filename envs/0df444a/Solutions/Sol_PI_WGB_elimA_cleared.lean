-- Prove2me | solution 1 for PI.WGB.elimA_cleared
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:19.57142+00:00
-- url     : https://prove2.me/submissions/2956bc9c-412a-4b5a-ae0e-7e267b07f69a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_PI_WGB_elimA_inv
import Theorems.Thm_PI_WGB_stepA_cleared
import Theorems.Thm_PI_WGB_pivotA_ne
import Theorems.Thm_PI_WGB_minorA_RInv
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_minor_CInv
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
theorem _root_.solution (x : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    ∀ k, k ≤ n → clearedA k (elimA k x) := by
  intro k
  induction k with
  | zero =>
    intro _ a j _ _ h
    omega
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hc := ih (by omega)
    simp only [elimA, dif_pos hkn]
    apply stepA_cleared k hkn _ hc
    apply pivotA_ne k hkn _ hc
    have hk1 : k + 1 ≤ n + 1 := by omega
    rw [elimA_inv (fun y => eval y (lpMinor ℂ (k + 1) hk1 hk1 :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ))
      (minorA_RInv _ _) (lhwline_minor_CInv _ _ _)]
    exact hx k hkn
end PI.WGB
