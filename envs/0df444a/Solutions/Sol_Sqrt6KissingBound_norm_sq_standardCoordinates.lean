-- Prove2me | solution 1 for Sqrt6KissingBound.norm_sq_standardCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:55.111075+00:00
-- url     : https://prove2.me/submissions/586114a5-3c5d-47f0-9ecc-819904831987

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) (t : ℝ) (v : Fin d → ℝ) :
    ‖standardCoordinates d (t, v)‖ ^ 2 =
      t ^ 2 + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [standardCoordinates, Fin.sum_univ_succ]
end Sqrt6KissingBound
