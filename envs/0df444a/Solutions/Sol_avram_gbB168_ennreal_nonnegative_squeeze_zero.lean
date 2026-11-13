-- Prove2me | solution 1 for avram_gbB168_ennreal_nonnegative_squeeze_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:26:34.902046+00:00
-- url     : https://prove2.me/submissions/f06ee43b-6fbf-4497-b1aa-6d4c8f6bc060

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal
noncomputable section

theorem solution (u v : ℕ → ℝ≥0∞)
    (hv : Tendsto v atTop (𝓝 (0 : ℝ≥0∞)))
    (hu : ∀ k, u k ≤ v k) :
    Tendsto u atTop (𝓝 (0 : ℝ≥0∞)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hv
    (Filter.Eventually.of_forall (fun k => bot_le))
    (Filter.Eventually.of_forall hu)
