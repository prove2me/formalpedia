-- Prove2me | solution 1 for SpectralRepresentation.stepDown_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:31:44.611326+00:00
-- url     : https://prove2.me/submissions/fff3299b-e0e8-448b-9415-7640b61b8846

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
namespace SpectralRepresentation
theorem _root_.solution (t : ℝ) (n : ℕ) {s : ℝ} (hs : t ≤ s) : stepDown t n s = 1 := by
  have h0 : 0 ≤ ((n : ℝ) + 1) * (s - t) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hs)
  rw [stepDown, min_eq_left (by linarith), max_eq_right zero_le_one]
end SpectralRepresentation
