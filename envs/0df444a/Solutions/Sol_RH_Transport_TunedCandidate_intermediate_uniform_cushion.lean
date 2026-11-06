-- Prove2me | solution 1 for RH.Transport.TunedCandidate.intermediate_uniform_cushion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:11.768709+00:00
-- url     : https://prove2.me/submissions/2927bae4-820a-4262-b30f-fc2c5867787d

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_intermediateExponent_le_corner
import Theorems.Thm_RH_Transport_TunedCandidate_intermediate_exceeds_cushion

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {δ x : ℝ}
    (hd0 : 0 ≤ δ) (hd : δ ≤ 3 / 4) (hx : x ≤ 1 / 2) :
    intermediateExponent δ x < -cushion := by
  have hm := intermediateExponent_le_corner hd0 hd hx
  have hc := intermediate_exceeds_cushion
  dsimp [sideMargin] at hc
  linarith
end RH.Transport.TunedCandidate
