-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_mul_5c83663d1f17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:41.297561+00:00
-- url     : https://prove2.me/submissions/76003523-e635-4318-9b60-02fedf5bc64c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863

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
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {F G : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖)
    (hG : IntSeriesConv G ‖z‖) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by
  have hF' : Summable fun n ↦ ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ := by
    simp only [norm_intSeries_term]; exact hF
  have hG' : Summable fun n ↦ ‖((coeff n G : ℤ) : ℂ) * z ^ n‖ := by
    simp only [norm_intSeries_term]; exact hG
  rw [intSeriesEval, intSeriesEval, intSeriesEval,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF' hG']
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul, Int.cast_sum, sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add, Int.cast_mul]
  ring
end GroundTheory.Heights₂.Heights.ChowlaSelberg
