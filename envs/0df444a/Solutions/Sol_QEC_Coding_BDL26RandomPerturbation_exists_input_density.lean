-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.exists_input_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:44.308853+00:00
-- url     : https://prove2.me/submissions/ef00f210-7eaf-4d6d-a3b5-d24f054f5f90

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (tPrime handoff : ℝ) :
    ∃ t : ℝ, 0 < t ∧ tPrime < t ∧ handoff < t := by
  refine ⟨max 0 (max tPrime handoff) + 1, ?_, ?_, ?_⟩
  · have := le_max_left (0 : ℝ) (max tPrime handoff); linarith
  · have := (le_max_left tPrime handoff).trans (le_max_right 0 (max tPrime handoff))
    linarith
  · have := (le_max_right tPrime handoff).trans (le_max_right 0 (max tPrime handoff))
    linarith
end QEC.Coding.BDL26RandomPerturbation
