-- Prove2me | solution 1 for UnifErgHW.Diffusion.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:44:23.598445+00:00
-- url     : https://prove2.me/submissions/92300f27-99fc-432d-9de3-91a1827f31af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Theorems.Thm_UnifErgHW_Diffusion_eq_2_28
import Theorems.Thm_UnifErgHW_Diffusion_theorem_2_1_b

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
open GPhNGIDiffusion.EMError (SolvesAdditiveSDE IsTransitionFunction IsInvariantMeasure generator tvNormWeighted cutoff partial2)

open UnifErgHW.Diffusion in
theorem solution {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m)
    (ϱ θ : ℝ) (hℓ : IsCentered D ϱ) (hϱ : 0 < ϱ) (hσ : IsNormalized D)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1)
    (hθ : 0 < θ) (h227 : θ ≤ ϱ / (3 * m * (2 * ϱ + m))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      (∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
          generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x
            ≤ κ₀ - ε * (ϱ / (2 * m) + θ / 2 * negL1 x) * lyapV D ε θ x) ∧
      ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
        ∀ v : EthierKurtz.SDEState m → Fin m → ℝ, IsMarkovControl v →
          ∀ P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m),
            IsMarkovTransition D v P →
            ∃ π : Measure (EthierKurtz.SDEState m), IsInvariantMeasure P π ∧
              ∫⁻ y, ENNReal.ofReal (lyapV D ε θ y) ∂π ≤
                ENNReal.ofReal (2 * m / (ε * ϱ) * κ₀) ∧
              ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState m),
                tvNormWeighted (lyapV D ε θ) (P t x) π
                  ≤ ENNReal.ofReal (C * lyapV D ε θ x * Real.exp (-γ * t)) := by
  obtain ⟨ε₀, hε₀, hA⟩ := eq_2_28 hm D ϱ θ hℓ hϱ hσ h215 hθ h227
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨κ₀, hκ₀, hdrift⟩ := hA ε hε hεle
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hκ₁ : 0 < ε * ϱ / (2 * m) := by positivity
  have h232 : ∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
      generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x ≤
        κ₀ - ε * ϱ / (2 * m) * lyapV D ε θ x := by
    intro x u hu
    have h := hdrift x u hu
    have hn : 0 ≤ negL1 x := Finset.sum_nonneg fun i _ => le_max_right _ _
    have hV : 0 < lyapV D ε θ x := Real.exp_pos _
    have : 0 ≤ ε * (θ / 2 * negL1 x) * lyapV D ε θ x := by positivity
    have e : ε * (ϱ / (2 * m) + θ / 2 * negL1 x) * lyapV D ε θ x =
        ε * ϱ / (2 * m) * lyapV D ε θ x + ε * (θ / 2 * negL1 x) * lyapV D ε θ x := by ring
    linarith
  obtain ⟨γ, C, hγ, hC, hB⟩ :=
    theorem_2_1_b hm D ϱ ε θ hℓ hϱ hε hθ κ₀ (ε * ϱ / (2 * m)) hκ₀ hκ₁ h232
  refine ⟨κ₀, hκ₀, hdrift, γ, C, hγ, hC, fun v hv P hP => ?_⟩
  obtain ⟨π, hπ, hint, htv⟩ := hB v hv P hP
  refine ⟨π, hπ, ?_, htv⟩
  have e : κ₀ / (ε * ϱ / (2 * m)) = 2 * m / (ε * ϱ) * κ₀ := by field_simp
  rwa [e] at hint
