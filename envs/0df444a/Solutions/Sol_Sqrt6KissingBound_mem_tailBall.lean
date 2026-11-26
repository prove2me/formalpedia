-- Prove2me | solution 1 for Sqrt6KissingBound.mem_tailBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:35.196938+00:00
-- url     : https://prove2.me/submissions/264fac1f-a18e-467d-baf5-666d8c1800e7

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution {d : ℕ} {r : ℝ} {v : Fin d → ℝ} :
    v ∈ tailBall d r ↔
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ < r := by
  simp [tailBall, mem_ball, dist_zero_right]
end Sqrt6KissingBound
