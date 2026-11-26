-- Prove2me | solution 1 for TunnellMap.orthogonalFrameExec_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:04.136195+00:00
-- url     : https://prove2.me/submissions/15189104-53b8-4f48-88e3-8e85c2cd081a

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
import Theorems.Thm_TunnellMap_frame_gram_det

set_option autoImplicit true
open TunnellMap
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (hp : tripleGCD p = 1) :
    dot (frameE₁ p) (frameE₁ p) * dot (frameE₂ p) (frameE₂ p) -
      dot (frameE₁ p) (frameE₂ p) ^ 2 = dot p p :=
  frame_gram_det (orthogonalFrameExec p hp)
end TunnellMap
