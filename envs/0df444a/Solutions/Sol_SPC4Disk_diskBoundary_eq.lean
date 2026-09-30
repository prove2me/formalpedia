-- Prove2me | solution 1 for SPC4Disk.diskBoundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T05:58:59.296678+00:00
-- url     : https://prove2.me/submissions/0adcc03f-470c-4936-a22b-46626e2b1fe4

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace SPC4Disk

lemma disk_isInteriorPoint
    {z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : ‖z.val‖ < 1) : (𝓡∂ (m + 1)).IsInteriorPoint z := by
  have hchart : chartAt (EuclideanHalfSpace (m + 1)) z =
      if ‖z.val‖ < 1 then DiskInteriorChart
      else DiskBoundaryChart (unitOr diskNorth z.val) := rfl
  rw [ModelWithCorners.IsInteriorPoint,
    interior_range_modelWithCornersEuclideanHalfSpace, extChartAt, hchart,
    if_pos h]
  show (0 : ℝ) < (z.val + diskShift (m + 1)) 0
  have hco : (z.val + diskShift (m + 1)) 0 = z.val 0 + 2 := by simp [diskShift]
  rw [hco]
  have h2 := abs_le.mp (le_trans (EuclideanSpace.abs_coord_le_norm _ 0) h.le)
  linarith [h2.1]

lemma disk_isBoundaryPoint
    {z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (h : ‖z.val‖ = 1) : (𝓡∂ (m + 1)).IsBoundaryPoint z := by
  have hchart : chartAt (EuclideanHalfSpace (m + 1)) z =
      if ‖z.val‖ < 1 then DiskInteriorChart
      else DiskBoundaryChart (unitOr diskNorth z.val) := rfl
  rw [ModelWithCorners.IsBoundaryPoint,
    frontier_range_modelWithCornersEuclideanHalfSpace, extChartAt, hchart,
    if_neg (by rw [h]; exact lt_irrefl 1)]
  show (0 : ℝ) =
    (DiskBoundaryChartFun (unitOr diskNorth z.val) z).val 0
  rw [DiskBoundaryChartFun_val_zero, h, sub_self]

end SPC4Disk

open SPC4Disk in
theorem solution :
    (𝓡∂ (m + 1)).boundary
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) =
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        ‖z.val‖ = 1 } := by
  ext z
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp z.2) with h | h
  · apply iff_of_false
    · rw [← mem_compl_iff, ModelWithCorners.compl_boundary]
      exact disk_isInteriorPoint h
    · exact fun h1 => absurd h1 (ne_of_lt h)
  · exact iff_of_true (disk_isBoundaryPoint h) h
