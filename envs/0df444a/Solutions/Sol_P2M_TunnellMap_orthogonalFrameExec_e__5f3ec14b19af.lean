-- Prove2me | solution 1 for P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:54.702871+00:00
-- url     : https://prove2.me/submissions/24b46b8c-2f5d-43f4-99d1-48919e1deec0

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).e₂ = frameE₂ p := rfl
end TunnellMap
