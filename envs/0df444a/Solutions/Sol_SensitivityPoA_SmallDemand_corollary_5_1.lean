-- Prove2me | solution 1 for SensitivityPoA.SmallDemand.corollary_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T09:05:49.837365+00:00
-- url     : https://prove2.me/submissions/36cda510-d016-422c-9228-8ca31b14ba5b

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting
import Theorems.Thm_SensitivityPoA_SmallDemand_poa_demandNormalize
import Theorems.Thm_SensitivityPoA_SmallDemand_poa_normalized_le

open SensitivityPoA.SmallDemand KellyStochasticNetworks

theorem solution (N : Network) (hN : N.Standing) (τ : Fin N.J → ℝ → ℝ)
    (hτ : ∀ j, IsCostFn (τ j)) (hpos : ∀ j, ∀ x, 0 ≤ x → 0 < τ j x)
    (b : ℝ) (hb : 0 < b) (Mτ : ℝ) (hM : 0 < Mτ) (hLip : ∀ j, LipOnIcc (τ j) b Mτ)
    (τmin : ℝ) (hτmin : IsLeast (Set.range fun j => τ j 0) τmin) :
    ∃ δ > 0, ∀ d : Fin N.Sd → ℝ, (∀ k, 0 ≤ d k) → 0 < totalDemand d → totalDemand d < δ →
      PoA (⟨τ, d⟩ : Game N) ≤
        1 + 8 * (N.J : ℝ) * ((N.Sd : ℝ) + 1) / τmin * Mτ * totalDemand d := by
  obtain ⟨δ, hδ, H⟩ := poa_normalized_le N hN τ hτ hpos b hb Mτ hM hLip τmin hτmin
  refine ⟨δ, hδ, fun d hd hT hTδ => ?_⟩
  obtain ⟨h1, h2⟩ := H d hd hT hTδ
  have hΓ : (⟨τ, d⟩ : Game N) ∈ gameSpace N :=
    ⟨⟨hτ, hd⟩, hT, fun j x hx _ => hpos j x hx.le⟩
  have hinv := (poa_demandNormalize (⟨τ, d⟩ : Game N) hΓ (totalDemand d) hT).2.2.2.2
  rw [hinv, h1] at h2
  have := (abs_le.mp h2).2
  linarith

