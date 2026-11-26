-- Prove2me | solution 1 for contDiff_polytopeSoftPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:39.989474+00:00
-- url     : https://prove2.me/submissions/49c16667-86fe-4055-85ca-6a2fcc687329

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Theorems.Thm_contDiff_polytopeDirectionalValue

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution (u : Finset ℂ) (delta : ℝ) :
    ContDiff ℝ ∞ (polytopeSoftPartition u delta) := by
  unfold polytopeSoftPartition
  apply ContDiff.sum
  intro z hz
  exact ((contDiff_polytopeDirectionalValue z).div_const delta).exp
