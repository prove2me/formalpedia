-- Prove2me | solution 1 for TunnellChallenge.sourceLift_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:00:26.387912+00:00
-- url     : https://prove2.me/submissions/dbd6f1d9-8e50-4d1d-87fb-8e4eecfe37a4

import Definitions.Def_TunnellMap_BranchSpec
import Definitions.Def_TunnellMap_Solution

set_option autoImplicit true
open TunnellChallenge
set_option maxHeartbeats 1000000
open Polynomial
namespace TunnellChallenge
theorem _root_.solution {n : ℤ} (s : BResidual n) :
    coreTriple (residualSourceLift s) =
      TunnellMap.residualSourceLift (brEquiv n s) := rfl
end TunnellChallenge
