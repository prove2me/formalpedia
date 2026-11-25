-- Prove2me | solution 1 for SpectralRepresentation.stepDown_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:47.798569+00:00
-- url     : https://prove2.me/submissions/d39912d4-2b12-4f4f-9b55-24b8c12bf299

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
theorem _root_.solution (t : ℝ) (n : ℕ) (s : ℝ) : 0 ≤ stepDown t n s :=
  le_max_left _ _
end SpectralRepresentation
