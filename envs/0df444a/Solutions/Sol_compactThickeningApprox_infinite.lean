-- Prove2me | solution 1 for compactThickeningApprox_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:39.95183+00:00
-- url     : https://prove2.me/submissions/e01d3bef-8910-472d-88fd-1aef8ba19c61

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
section
open Metric Set
private theorem smoothApproxRadius_pos_compact (n : ℕ) : 0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity
end

set_option autoImplicit false
open Metric Set
theorem _root_.solution (K : Set ℂ) (n : ℕ)
    (hnonempty : K.Nonempty) : (compactThickeningApprox K n).Infinite := by
  obtain ⟨z, hz⟩ := hnonempty
  have hball : (Metric.closedBall z (smoothApproxRadius n)).Infinite := by
    have hopen : (Metric.ball z (smoothApproxRadius n)).Infinite := by
      apply Set.Infinite.of_accPt
      exact Metric.isOpen_ball.preperfect z
        (Metric.mem_ball_self (smoothApproxRadius_pos_compact n))
    exact hopen.mono Metric.ball_subset_closedBall
  apply hball.mono
  unfold compactThickeningApprox
  exact Metric.closedBall_subset_cthickening hz _
