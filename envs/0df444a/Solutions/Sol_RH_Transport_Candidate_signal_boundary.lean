-- Prove2me | solution 1 for RH.Transport.Candidate.signal_boundary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:26.420523+00:00
-- url     : https://prove2.me/submissions/7ebaf1ea-61f6-40bf-8531-846e477af890

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution : signal p B = lowExponent p := by
  unfold signal lowExponent B h b boundary
  ring
