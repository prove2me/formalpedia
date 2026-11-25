-- Prove2me | solution 1 for PI.WGB.stepA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:49.607991+00:00
-- url     : https://prove2.me/submissions/3e96ce61-125b-4a66-9fa6-df3ecc51a4b4

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
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
theorem _root_.solution (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a j : Fin (n + 1)) :
    stepA p q x (a, j) =
      (if p < a ∧ a.val < n then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a ∧ a.val < n then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by
  simp only [stepA, lhwline_mcol, lhwline_mrow, Finset.mem_filter, Finset.mem_univ, true_and,
    lt_irrefl, false_and, if_false]
  split_ifs <;> ring
end PI.WGB
