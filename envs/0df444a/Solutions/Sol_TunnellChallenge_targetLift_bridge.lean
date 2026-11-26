-- Prove2me | solution 1 for TunnellChallenge.targetLift_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:00:41.638739+00:00
-- url     : https://prove2.me/submissions/35548b72-01fc-4d40-8ccf-cedcbf80b035

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution

set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (t : AResidual n) :
    coreTriple (residualTargetLift t) =
      TunnellMap.residualTargetLift (arEquiv n t) := rfl
end TunnellChallenge
