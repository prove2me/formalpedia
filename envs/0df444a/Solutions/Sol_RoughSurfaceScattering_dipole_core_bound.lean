-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_core_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T05:55:11.594071+00:00
-- url     : https://prove2.me/submissions/fd8165a7-11bc-4191-bdcd-e996e8dab324
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_dipole_h1_core
import Theorems.Thm_RoughSurfaceScattering_vCorr_l2_bound

open MeasureTheory
open RoughSurfaceScattering

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ u : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u j).1 (u j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
                dipoleSource km (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
                vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) ≤ ENNReal.ofReal C ∧
            l2Norm D0 (vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ1, hδ1, hH⟩ := dipole_h1_core f hf lam hlam0 hlam1 hf2 kp km μ hpar s0
  obtain ⟨δ2, hδ2, hL⟩ := vCorr_l2_bound f hf lam hlam0 hlam1 hf2 μ s0
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun δ hδ hδ0 D0 hD0 hball hsub u hu => ?_⟩
  obtain ⟨C1, hC1⟩ := hH δ hδ (lt_of_lt_of_le hδ0 (min_le_left _ _)) D0 hD0 hball hsub u hu
  obtain ⟨C2, hC2⟩ := hL δ hδ (lt_of_lt_of_le hδ0 (min_le_right _ _)) D0 hD0 hball hsub
  exact ⟨max C1 C2, fun j hj =>
    ⟨(hC1 j hj).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
     (hC2 j hj).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩⟩
