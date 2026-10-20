-- Prove2me | solution 1 for PDSmooth.Framework.corollary_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:15:12.188462+00:00
-- url     : https://prove2.me/submissions/f0b4e2c1-86d7-4b54-8ad3-b1284eeb0876

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting
import Theorems.Thm_PDSmooth_Framework_theorem_4_1
import Theorems.Thm_PDSmooth_Framework_theorem_4_2

open Filter Topology

namespace PDSmoothSol
open PDSmooth.Framework

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ε η qstar : ℝ) (hlam0 : 0.8 * γ⁻¹ < lam) (hlam1 : lam < γ⁻¹) (hε : 0 < ε)
    (hη : η = ε ^ 2 * lam * (1 - γ * lam) / (32 * βX ^ 2))
    (hqstar : ∀ z ∈ X, qstar ≤ qObj Φ g r Y z)
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x) :
    ∃ K : ℕ, 1 ≤ K ∧
      (K : ℤ) ≤ ⌈32 * βX ^ 2 * (qObj Φ g r Y (x 1) - qstar) / (5 * ε ^ 2 * lam * (γ * lam - 0.8))⌉ + 1 ∧
      Stops γ lam η x K ∧ (∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j) ∧
      IsNSPoint (qObj Φ g r Y) ωX X γ βX ε (x K) := by
  have hγ := hA.γ_pos
  have hlam0' : 0 < lam := lt_trans (by positivity) hlam0
  have hγl : γ * lam < 1 := by
    have := (lt_inv_comm₀ hlam0' hγ).mp hlam1
    have h2 : γ * lam < lam⁻¹ * lam := mul_lt_mul_of_pos_right this hlam0'
    rwa [inv_mul_cancel₀ hlam0'.ne'] at h2
  have hβ : 0 < βX := lt_of_lt_of_le one_pos hA.βX_ge
  have hηpos : 0 < η := by
    rw [hη]; have : 0 < 1 - γ * lam := by linarith
    positivity
  obtain ⟨K, hK1, hKle, hKs, hKf⟩ := PDSmooth.Framework.theorem_4_2 hA lam η qstar hlam0 hlam1 hηpos hqstar x hx
  have hNS := (PDSmooth.Framework.theorem_4_1 hA lam ε η hlam0' hlam1 hε hη x hx K hK1 hKs hKf).2
  refine ⟨K, hK1, ?_, hKs, hKf, hNS⟩
  have heq : (qObj Φ g r Y (x 1) - qstar) / ((γ * lam / (1 - γ * lam) - 4) * η) =
      32 * βX ^ 2 * (qObj Φ g r Y (x 1) - qstar) / (5 * ε ^ 2 * lam * (γ * lam - 0.8)) := by
    have h1 : 1 - γ * lam ≠ 0 := by linarith
    have h08 : γ * lam - 0.8 ≠ 0 := by
      have := mul_lt_mul_of_pos_left hlam0 hγ
      rw [mul_left_comm, mul_inv_cancel₀ hγ.ne', mul_one] at this
      linarith
    have h3 : γ * lam / (1 - γ * lam) - 4 = 5 * (γ * lam - 0.8) / (1 - γ * lam) := by
      field_simp; norm_num; ring
    rw [h3, hη]
    field_simp
  rw [← heq]; exact hKle
