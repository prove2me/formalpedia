-- Prove2me | solution 1 for PI.WGB.mrow_invA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:57.459524+00:00
-- url     : https://prove2.me/submissions/b01d99ad-3eaf-446b-9822-e4eac17366dd

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
theorem _root_.solution (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hφ : RInvA φ) (p : Fin (n + 1))
    (t : Fin (n + 1) → ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (S : Finset (Fin (n + 1)))
    (hS : ∀ b ∈ S, p < b ∧ b.val < n) :
    φ (lhwline_mrow p S t x) = φ x := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
  | insert b S hb ih =>
    have hpS : p ∉ S := fun h => lt_irrefl p (hS p (Finset.mem_insert_of_mem h)).1
    have hpb := hS b (Finset.mem_insert_self b S)
    have heq : lhwline_mrow p (insert b S) t x = lhwline_rowOp p b (t b) (lhwline_mrow p S t x) := by
      funext v
      simp only [lhwline_mrow, lhwline_rowOp, Finset.mem_insert]
      by_cases hv : v.1 = b
      · simp [hv, hb, hpS]
      · simp [hv]
    rw [heq, hφ _ p b _ hpb.1 hpb.2, ih fun b' hb' => hS b' (Finset.mem_insert_of_mem hb')]
end PI.WGB
