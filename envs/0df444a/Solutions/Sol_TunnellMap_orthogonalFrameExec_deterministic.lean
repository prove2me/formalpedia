-- Prove2me | solution 1 for TunnellMap.orthogonalFrameExec_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:08.758736+00:00
-- url     : https://prove2.me/submissions/b8e0478a-b1a0-443d-bf07-9b1dfefe8974

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (p : Triple) (hp hp' : tripleGCD p = 1) :
    orthogonalFrameExec p hp = orthogonalFrameExec p hp' := rfl
end TunnellMap
