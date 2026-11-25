-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pow_36e45add25b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:59.466414+00:00
-- url     : https://prove2.me/submissions/09ebd1fd-783b-4c4a-813e-b62c17684d89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_mul_8992812ba236
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_one_7baeda032aea

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
theorem _root_.solution {F : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (m : ℕ) : IntSeriesConv (F ^ m) r := by
  induction m with
  | zero => simpa using intSeriesConv_one
  | succ m ih => rw [pow_succ]; exact intSeriesConv_mul hr ih hF
end GroundTheory.Heights₂.Heights.ChowlaSelberg
