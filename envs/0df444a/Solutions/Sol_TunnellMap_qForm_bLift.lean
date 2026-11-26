-- Prove2me | solution 1 for TunnellMap.qForm_bLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:22.659732+00:00
-- url     : https://prove2.me/submissions/d2c98723-1f0d-404b-8d8e-9d80d0d231f0

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : BOddRep n) : qForm (bLift p) = n := by
  have h := p.2.1
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 = n at h
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 2 * (2 * p.1.z) ^ 2 = n
  nlinarith
end TunnellMap
