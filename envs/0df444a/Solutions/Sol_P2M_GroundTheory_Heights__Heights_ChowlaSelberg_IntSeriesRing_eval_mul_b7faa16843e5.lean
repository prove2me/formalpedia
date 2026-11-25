-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_mul_b7faa16843e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:34.036286+00:00
-- url     : https://prove2.me/submissions/83caebf0-1b24-4de7-94c4-7977b345f6fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_summable_norm_term_3f2dc9731624

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
theorem _root_.solution {F G : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) (hG : IntSeriesConv G r)
    {z : ℂ} (hz : ‖z‖ ≤ r) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by
  unfold intSeriesEval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_term hF hz)
    (summable_norm_term hG hz)]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul]
  push_cast
  rw [sum_mul]
  refine sum_congr rfl fun q hq ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, pow_add]
  ring
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
