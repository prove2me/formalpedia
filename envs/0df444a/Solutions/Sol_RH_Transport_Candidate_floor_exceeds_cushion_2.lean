-- Prove2me | solution 2 for RH.Transport.Candidate.floor_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:11.232081+00:00
-- url     : https://prove2.me/submissions/6efefe1a-0dd8-4808-a964-4a99b8a63dcd

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution :
    cushion - 2 * zeta < sideMargin .floor - 2 * zeta := by
  norm_num [cushion, zeta, sideMargin, p]
end RH.Transport.Candidate
