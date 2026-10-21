-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:59:32.17099+00:00
-- url     : https://prove2.me/submissions/75d68ec4-b88b-4d2c-bd42-350bb30c9936

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_5_centered

open Filter Topology
open RandomLeadGBS.Diffusion

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    (∀ r : ℝ, 0 < r → ∃ p : ℤ → ℝ, IsArtStationary P r p) ∧
    ∀ p : ℝ → ℤ → ℝ, (∀ᶠ r in atTop, IsArtStationary P r (p r)) →
      (∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun r => ∑' j : ℤ, p r j * g ((j : ℝ) / Real.sqrt r)) atTop
          (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max ((j : ℝ) / Real.sqrt r) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) ∧
      Tendsto (fun r => ∑' j : ℤ, p r j * max (-((j : ℝ) / Real.sqrt r)) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) := by
  have h := lemma_5_centered P hP
  simp only [hx, sub_zero] at h
  exact h
