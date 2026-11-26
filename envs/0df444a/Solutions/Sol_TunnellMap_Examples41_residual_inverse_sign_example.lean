-- Prove2me | solution 1 for TunnellMap.Examples41.residual_inverse_sign_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:54.748196+00:00
-- url     : https://prove2.me/submissions/e91e3709-b810-45bd-9a0d-370d35e7d7ea

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    negTriple (residualTargetLift t2) = ⟨4, -3, 0⟩ ∧
      negTriple (negTriple (residualSourceLift s2)) = residualSourceLift s2 ∧
      s2.1.1 = ⟨-2, -5, 1⟩ := by
  norm_num [t2, s2, midpointSource, residualTargetLift, residualSourceLift,
    aLift, bLift, negTriple]
end TunnellMap.Examples41
