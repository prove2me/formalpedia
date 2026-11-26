-- Prove2me | solution 1 for contDiff_polytopeDirectionalValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:39.687569+00:00
-- url     : https://prove2.me/submissions/b55af1e3-376e-4065-8bb3-e306b78f0bdd

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (z : ℂ) :
    ContDiff ℝ ∞ (polytopeDirectionalValue z) := by
  unfold polytopeDirectionalValue
  exact (contDiff_const.mul Real.contDiff_cos).add
    (contDiff_const.mul Real.contDiff_sin)
