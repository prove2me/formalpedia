-- Prove2me | solution 1 for TunnellMap.orthogonalFrameExec_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:55.643015+00:00
-- url     : https://prove2.me/submissions/6e6c892e-0594-4a87-9e84-62f055c75b5c

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).z = tripleBezout p := rfl
end TunnellMap
