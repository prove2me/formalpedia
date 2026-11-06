-- Prove2me | solution 1 for RH.Transport.TunedCandidate.intermediateExponent_le_corner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:38.159992+00:00
-- url     : https://prove2.me/submissions/6cc645a6-279e-4b98-8fc9-eb1fba5463f0

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_intermediateExponent_eq

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution {δ x : ℝ}
    (hd0 : 0 ≤ δ) (hd : δ ≤ 3 / 4) (hx : x ≤ 1 / 2) :
    intermediateExponent δ x ≤ intermediateExponent (3 / 4) (1 / 2) := by
  have hm : δ * x ≤ δ * (1 / 2) :=
    mul_le_mul_of_nonneg_left hx hd0
  rw [intermediateExponent_eq, intermediateExponent_eq]
  nlinarith
end RH.Transport.TunedCandidate
