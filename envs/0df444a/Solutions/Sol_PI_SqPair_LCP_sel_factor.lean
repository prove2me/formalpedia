-- Prove2me | solution 1 for PI.SqPair.LCP.sel_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:35.253724+00:00
-- url     : https://prove2.me/submissions/44c79d98-b6e5-451b-8df7-d9e376c25764

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]
namespace PI.SqPair.LCP
theorem _root_.solution (ϖ : R) (hϖ0 : ϖ ≠ 0)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι κ : Type} (h : Matrix ι κ R) (hh : h ≠ 0) :
    ∃ (m : ℕ) (h₁ : Matrix ι κ R) (i : ι) (j : κ), h = ϖ ^ m • h₁ ∧ IsUnit (h₁ i j) := by
  classical
  have hex : ∃ n : ℕ, ∃ i j, h i j ≠ 0 ∧ ∃ u : R, IsUnit u ∧ h i j = ϖ ^ n * u := by
    by_contra hne
    apply hh
    ext i j
    rw [Matrix.zero_apply]
    by_contra hij
    obtain ⟨n, u, hu, he⟩ := hval _ hij
    exact hne ⟨n, i, j, hij, u, hu, he⟩
  obtain ⟨i₀, j₀, _, u₀, hu₀, he₀⟩ := Nat.find_spec hex
  have hdiv : ∀ i j, ∃ z : R, h i j = ϖ ^ Nat.find hex * z := by
    intro i j
    by_cases hij : h i j = 0
    · exact ⟨0, by rw [hij, mul_zero]⟩
    · obtain ⟨n, u, hu, he⟩ := hval _ hij
      have hmn : Nat.find hex ≤ n := Nat.find_min' hex ⟨i, j, hij, u, hu, he⟩
      refine ⟨ϖ ^ (n - Nat.find hex) * u, ?_⟩
      rw [he, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
  choose h₁ hh₁ using hdiv
  refine ⟨Nat.find hex, Matrix.of h₁, i₀, j₀, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact hh₁ i j
  · have e : h₁ i₀ j₀ = u₀ :=
      mul_left_cancel₀ (pow_ne_zero _ hϖ0) ((hh₁ i₀ j₀).symm.trans he₀)
    simp only [Matrix.of_apply, e]
    exact hu₀
end PI.SqPair.LCP
