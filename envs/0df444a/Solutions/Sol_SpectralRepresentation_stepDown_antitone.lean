-- Prove2me | solution 1 for SpectralRepresentation.stepDown_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:13.029731+00:00
-- url     : https://prove2.me/submissions/6b8461fa-75b9-41b2-87d6-fbf51dc8fa5c

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
public import Theorems.Thm_SpectralRepresentation_stepDown_eq_one

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
namespace SpectralRepresentation
theorem _root_.solution (t s : ℝ) : Antitone (fun n => stepDown t n s) := by
  intro m n hmn
  show stepDown t n s ≤ stepDown t m s
  rcases le_total t s with hts | hst
  · rw [stepDown_eq_one t n hts, stepDown_eq_one t m hts]
  · refine max_le_max le_rfl (min_le_min le_rfl ?_)
    have hst' : s - t ≤ 0 := by linarith
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith [hst', hmn']
end SpectralRepresentation
