-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.polydisc_cons_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:35.690288+00:00
-- url     : https://prove2.me/submissions/53ec1072-a6a0-45df-bda0-d173af517be3

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {R : ℝ} (hR : 0 < R) {x : ℂ} {y : Fin D → ℂ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) : (Fin.cons x y : Fin (D + 1) → ℂ) ∈ Metric.ball 0 R := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hR]
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · simpa using hx
  · simpa using (pi_norm_lt_iff hR).1 hy j
end ReciprocityTheory.GeometryOfNumbersTheory
