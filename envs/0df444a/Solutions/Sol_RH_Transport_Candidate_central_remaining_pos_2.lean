-- Prove2me | solution 2 for RH.Transport.Candidate.central_remaining_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:02.701699+00:00
-- url     : https://prove2.me/submissions/5cf5ddd8-8a97-4ea2-baa3-fa7e100a3a03

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution : 0 < cushion - 2 * zeta := by
  norm_num [cushion, zeta]
end RH.Transport.Candidate
