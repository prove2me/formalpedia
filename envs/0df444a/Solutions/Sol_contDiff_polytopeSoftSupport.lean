-- Prove2me | solution 1 for contDiff_polytopeSoftSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:03.199116+00:00
-- url     : https://prove2.me/submissions/74ad8e76-591a-4e69-ab56-881499342be4

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Theorems.Thm_polytopeSoftPartition_pos
import Theorems.Thm_contDiff_polytopeSoftPartition

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {u : Finset ℂ} (hu : u.Nonempty)
    (delta : ℝ) :
    ContDiff ℝ ∞ (polytopeSoftSupport u delta) := by
  unfold polytopeSoftSupport
  exact contDiff_const.mul ((contDiff_polytopeSoftPartition u delta).log
    (fun theta => (polytopeSoftPartition_pos hu delta theta).ne'))
