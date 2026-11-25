-- Prove2me | solution 1 for PI.EF.zeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:03:52.289511+00:00
-- url     : https://prove2.me/submissions/5b3bad9a-1ee1-4566-896d-aa7f5ec1ad79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Theorems.Thm_PI_EF_level_eq_one_of_primitive_one
import Theorems.Thm_PI_EF_completed_ne_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution : ZeroLocus := by
  intro N _ χ hχ s hs hs1 hL
  by_cases hre1 : 1 ≤ s.re
  · exact absurd hL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre1)
  by_cases hre0 : 0 < s.re
  · left
    exact ⟨hre0, by linarith⟩
  push_neg at hre1 hre0
  right
  by_cases hc : s = 0 ∧ χ = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := hc
    have hN := level_eq_one_of_primitive_one hχ rfl
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by tauto
  have hne := completed_ne_zero_left hχ hre0 hc'
  have hsN : s ≠ 0 ∨ N ≠ 1 := by
    rcases hc' with h | h
    · right
      intro hN
      subst hN
      exact h (DirichletCharacter.level_one χ)
    · left
      exact h
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hsN
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  rcases hdiv with h | hg
  · exact absurd h hne
  rcases DirichletCharacter.even_or_odd χ with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    simp at hn
    refine Or.inl ⟨hn, he, ?_⟩
    intro h1
    exact hc ⟨hn, h1⟩
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    refine Or.inr ⟨?_, ho⟩
    simp at hn
    linear_combination hn
end PI.EF
