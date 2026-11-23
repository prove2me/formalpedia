-- Prove2me | solution 1 for SumProduct.volume_cubeSection_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:07:33.450347+00:00
-- url     : https://prove2.me/submissions/5cc4c9e7-c511-495f-9e12-1188336af6db

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution (r : ℝ) : volume (cubeSection ι r) ≠ ⊤ :=
  ne_top_of_le_ne_top (isCompact_closedBall (0 : ι → ℝ) |r|).measure_lt_top.ne
    (measure_mono fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
      intro i
      rw [Real.norm_eq_abs]
      exact le_trans (hy.1 i) (le_abs_self r))
end SumProduct
