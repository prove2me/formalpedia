-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_tsp_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-26T15:13:55.354019+00:00
-- url     : https://prove2.me/submissions/555681e4-e92f-4f94-9d33-845232add191
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_tsp_exists
import Theorems.Thm_RoughSurfaceScattering_dipole_data_holder

open MeasureTheory
open RoughSurfaceScattering

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ) (hpar : ParamCond kp km μ)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) :
    ∃ u : (R2 → ℂ) × (R2 → ℂ), IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u.1 u.2 := by
  obtain ⟨h1, h2⟩ := dipole_data_holder f hf kp hpar.1 z hz ν
  exact tsp_exists f hf kp km μ hpar (1 / 2) (by norm_num) (by norm_num) _ _ h1 h2
