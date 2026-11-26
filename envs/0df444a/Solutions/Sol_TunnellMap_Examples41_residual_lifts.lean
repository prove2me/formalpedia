-- Prove2me | solution 1 for TunnellMap.Examples41.residual_lifts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:13.98096+00:00
-- url     : https://prove2.me/submissions/ea8a62b5-460e-4576-8430-8cf69208166c

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    residualSourceLift s1 = ⟨-2, -5, -2⟩ ∧
      residualSourceLift s2 = ⟨-2, -5, 2⟩ ∧
      residualSourceLift s3 = ⟨-2, 5, -2⟩ ∧
      residualSourceLift s4 = ⟨-2, 5, 2⟩ ∧
      residualTargetLift t1 = ⟨-4, -3, 0⟩ ∧
      residualTargetLift t2 = ⟨-4, 3, 0⟩ ∧
      residualTargetLift t3 = ⟨0, -3, -4⟩ ∧
      residualTargetLift t4 = ⟨0, -3, 4⟩ := by
  norm_num [s1, s2, s3, s4, t1, t2, t3, t4, residualSourceLift,
    residualTargetLift, bLift, aLift, midpointSource]
end TunnellMap.Examples41
