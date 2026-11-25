-- Prove2me | solution 1 for SpectralRepresentation.stepDown_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:05.992204+00:00
-- url     : https://prove2.me/submissions/883942e7-08be-4dc1-9733-d0c0ac833795

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
theorem _root_.solution (t : ℝ) (n : ℕ) (s : ℝ) : stepDown t n s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
end SpectralRepresentation
