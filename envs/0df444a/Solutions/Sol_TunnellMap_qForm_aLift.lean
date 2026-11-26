-- Prove2me | solution 1 for TunnellMap.qForm_aLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:23.688386+00:00
-- url     : https://prove2.me/submissions/316b592e-7859-47d2-bf42-d90978a81393

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : ARep n) : qForm (aLift p) = n := by
  have h := p.2
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 = n at h
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 2 * (4 * p.1.z) ^ 2 = n
  nlinarith
end TunnellMap
