-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_pow_1a9d7efbc52a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:39.15436+00:00
-- url     : https://prove2.me/submissions/4b5894f1-9466-49d0-8ff3-b81a7cefcd80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_mul_5c83663d1f17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_one_d2caeccb4511
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5

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
theorem _root_.solution {F : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖) (m : ℕ) :
    intSeriesEval (F ^ m) z = intSeriesEval F z ^ m := by
  induction m with
  | zero => simpa using intSeriesEval_one z
  | succ m ih =>
    rw [pow_succ, intSeriesEval_mul (intSeriesConv_pow (norm_nonneg z) hF m) hF, ih, pow_succ]
end GroundTheory.Heights₂.Heights.ChowlaSelberg
