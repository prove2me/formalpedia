-- Prove2me | solution 1 for PI.WGB.stepA_cleared
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:27:59.2771+00:00
-- url     : https://prove2.me/submissions/5dabad2b-96af-4484-9b35-fe30d170841b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_PI_WGB_stepA_apply
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
theorem _root_.solution (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hp : y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0) :
    clearedA (k + 1) (stepA ⟨k, by omega⟩ ⟨k, by omega⟩ y) := by
  intro a j ha hne hlt
  rw [stepA_apply]
  simp only [Fin.lt_def]
  rcases lt_trichotomy j.val k with hj | hj | hj
  · have h1 : y (⟨k, by omega⟩, j) = 0 := hy _ _ (by show k < n; omega) (by show k ≠ j.val; omega) (Or.inr hj)
    have h2 : y (a, j) = 0 := hy _ _ ha hne (Or.inr hj)
    rw [if_neg (show ¬ k < j.val by omega)]
    split_ifs <;> simp [h1, h2]
  · have hjq : j = ⟨k, by omega⟩ := Fin.ext hj
    rw [hjq]
    simp only [Fin.val_mk, lt_irrefl, if_false, add_zero]
    split_ifs with ha'
    · rw [neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]
    · rw [← hjq]
      exact hy _ _ ha hne (Or.inl (by omega))
  · have ha2 : a.val ≤ k := by omega
    have hka : ¬ (k < a.val ∧ a.val < n) := by omega
    simp only [if_neg hka, if_pos hj]
    rcases lt_or_eq_of_le ha2 with ha2 | ha2
    · have h1 : y (a, j) = 0 := hy _ _ ha hne (Or.inl ha2)
      have h2 : y (a, ⟨k, by omega⟩) = 0 := hy _ _ ha (by show a.val ≠ k; omega) (Or.inl ha2)
      simp [h1, h2]
    · have hap : a = ⟨k, by omega⟩ := Fin.ext ha2
      rw [hap, neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]
end PI.WGB
