-- Prove2me | solution 1 for RobustPower.StochGap.eq_2_9_2_10_doubled_solution_robust_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:54:38.58679+00:00
-- url     : https://prove2.me/submissions/a0977c44-9a84-43b5-963d-14f1b13c43d7

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

set_option autoImplicit false

universe u

open Matrix RobustPower.StochGap in
theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (I₁ : Set (Fin n₁)) (ω₀ : Ω)
    (hsym : IsSymmetricAbout (Set.range b) (b ω₀))
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) (hx : x ∈ mixedIntDomain I₁) (hy : 0 ≤ y)
    (hfeas : b ω₀ ≤ A *ᵥ x + B *ᵥ y) :
    (∀ ω, b ω ≤ (2 : ℝ) • b ω₀) ∧
      RobFeasible A B b I₁ ∅ ((2 : ℝ) • x) ((2 : ℝ) • y) := by
  have h1 : ∀ ω, b ω ≤ (2 : ℝ) • b ω₀ := by
    intro ω
    obtain ⟨_, hs⟩ := hsym
    have hmem : b ω₀ + (b ω - b ω₀) ∈ Set.range b := by
      rw [add_sub_cancel]; exact Set.mem_range_self ω
    obtain ⟨ω', hω'⟩ := (hs _).1 hmem
    intro i
    have hi := hb ω' i
    rw [hω'] at hi
    simp only [Pi.sub_apply, Pi.zero_apply] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  refine ⟨h1, ⟨?_, ?_, ?_⟩⟩
  · refine ⟨smul_nonneg (by norm_num) hx.1, fun i hi => ?_⟩
    obtain ⟨z, hz⟩ := hx.2 i hi
    exact ⟨2 * z, by simp [hz]⟩
  · exact ⟨smul_nonneg (by norm_num) hy, fun i hi => absurd hi (Set.notMem_empty i)⟩
  · intro ω
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add]
    exact (h1 ω).trans (smul_le_smul_of_nonneg_left hfeas (by norm_num))
