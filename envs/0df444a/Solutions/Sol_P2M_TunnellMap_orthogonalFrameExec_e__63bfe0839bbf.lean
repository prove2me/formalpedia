-- Prove2me | solution 1 for P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:51.430665+00:00
-- url     : https://prove2.me/submissions/c2deda44-8eb7-4b78-a22d-aaa64e26bd57

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).e₁ = frameE₁ p := rfl
end TunnellMap
