-- Prove2me | solution 1 for TunnellMap.orthogonalFrameExec_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:22.961412+00:00
-- url     : https://prove2.me/submissions/c779b306-0997-49c9-ab18-2071e635f27b

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
import Theorems.Thm_TunnellMap_frame_orthogonal

set_option autoImplicit true
open TunnellMap
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (hp : tripleGCD p = 1) :
    dot p (frameE₁ p) = 0 ∧ dot p (frameE₂ p) = 0 :=
  frame_orthogonal (orthogonalFrameExec p hp)
end TunnellMap
