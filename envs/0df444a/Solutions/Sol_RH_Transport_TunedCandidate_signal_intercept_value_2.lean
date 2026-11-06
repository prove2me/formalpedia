-- Prove2me | solution 2 for RH.Transport.TunedCandidate.signal_intercept_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:59.461544+00:00
-- url     : https://prove2.me/submissions/18e1378c-e2f1-4a73-9551-8647073ed174

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
import Theorems.Thm_RH_Transport_TunedCandidate_signal_eq
import Theorems.Thm_RH_Transport_Geometry_signal_eq


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (s : ℝ) :
    signal s = s - 2147607 / 3125000 := by
  rw [signal_eq]
  norm_num [b]
  ring
end RH.Transport.TunedCandidate
