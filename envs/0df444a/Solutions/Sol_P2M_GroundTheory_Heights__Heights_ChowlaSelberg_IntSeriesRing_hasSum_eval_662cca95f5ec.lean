-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_hasSum_eval_662cca95f5ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:35.305849+00:00
-- url     : https://prove2.me/submissions/37f56cad-9936-49ce-97eb-03c6498fa3c8

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
theorem _root_.solution {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : HasSum (fun n ↦ ((coeff n F : ℤ) : ℂ) * z ^ n) (intSeriesEval F z) :=
  (summable_norm_term hF hz).of_norm.hasSum
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
