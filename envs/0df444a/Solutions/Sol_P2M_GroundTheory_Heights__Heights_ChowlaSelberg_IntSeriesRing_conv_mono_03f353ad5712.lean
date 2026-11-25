-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_mono_03f353ad5712
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:30.761024+00:00
-- url     : https://prove2.me/submissions/9594fae9-9b8a-46a7-9dd1-b8705a3ad8e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing

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
theorem _root_.solution {F : PowerSeries ℤ} {r r' : ℝ} (hF : IntSeriesConv F r) (h0 : 0 ≤ r')
    (hle : r' ≤ r) : IntSeriesConv F r' :=
  Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg h0 n))
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle n) (abs_nonneg _)) hF
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
