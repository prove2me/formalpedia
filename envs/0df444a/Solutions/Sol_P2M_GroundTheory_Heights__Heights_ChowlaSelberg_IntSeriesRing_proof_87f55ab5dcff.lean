-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_proof_87f55ab5dcff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:29.097645+00:00
-- url     : https://prove2.me/submissions/84f9569b-8180-4e82-852f-11dd857b1995

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_mono_03f353ad5712
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_hasSum_eval_662cca95f5ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_mul_b7faa16843e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_conv_expand_81eea0c6186f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_eval_expand_20c081d9dab8

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
theorem _root_.solution : IntSeriesRing.Statement := fun r hr ↦
  ⟨⟨convSubring r hr, fun _ ↦ Iff.rfl⟩,
    fun _ _ hF hG _ hz ↦ eval_mul hF hG hz,
    fun _ hF _ hz ↦ hasSum_eval hF hz,
    fun _ _ hF h0 hle ↦ conv_mono hF h0 hle,
    fun _ hp F hF ↦ ⟨conv_expand hp hF, fun z _ ↦ eval_expand hp F z⟩⟩
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
