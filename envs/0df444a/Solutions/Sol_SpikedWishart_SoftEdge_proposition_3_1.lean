-- Prove2me | solution 1 for SpikedWishart.SoftEdge.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:47:58.009734+00:00
-- url     : https://prove2.me/submissions/10b21053-13d0-4840-8282-3198d234c8a3

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
import Theorems.Thm_SpikedWishart_SoftEdge_proposition_3_1_i
import Theorems.Thm_SpikedWishart_SoftEdge_proposition_3_1_ii

open Complex SpikedWishart.SoftEdge in
theorem solution (ε γ₀ c₀ : ℝ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀)
    (r k : ℕ) (hkr : k ≤ r) :
    (∀ U₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cΓ ρΓ cH u : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |pc γ - cΓ| < ρΓ → (∀ j, |π j - cΓ| < ρΓ) → |1 - cΓ| < ρΓ → qM γ ε M < cΓ - ρΓ →
        -ε < cH → cH < 0 → U₀ ≤ u →
        ‖ZM γ (qM γ ε M) M k π * Hcal γ (qM γ ε M) M k π cΓ ρΓ u - Hinf ε k cH u‖ ≤
          C * Real.exp (-c * u) / (M : ℝ) ^ (1 / 3 : ℝ)) ∧
    (∀ V₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cS ρS cJ v : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |cS| < ρS → cS + ρS < qM γ ε M →
        cJ < -ε → V₀ ≤ v →
        ‖Jcal γ (qM γ ε M) M k π cS ρS v / ZM γ (qM γ ε M) M k π - Jinf ε k cJ v‖ ≤
          C * Real.exp (-c * v) / (M : ℝ) ^ (1 / 3 : ℝ)) := by
  exact ⟨SpikedWishart.SoftEdge.proposition_3_1_i ε γ₀ c₀ hε hγ₀ hc₀ r k hkr,
    SpikedWishart.SoftEdge.proposition_3_1_ii ε γ₀ c₀ hε hγ₀ hc₀ r k hkr⟩
