-- Prove2me | solution 1 for SpectralRepresentation.stepDown_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:44.234507+00:00
-- url     : https://prove2.me/submissions/3918ee28-a21f-4cde-a722-10a7cb461e95

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
theorem _root_.solution (t : ℝ) (n : ℕ) : Continuous (stepDown t n) := by
  unfold stepDown; fun_prop
end SpectralRepresentation
