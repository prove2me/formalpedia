-- Prove2me | solution 1 for TunnellMap.frame_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:56.190574+00:00
-- url     : https://prove2.me/submissions/16958664-7853-474c-bfb0-f32d2ad5aca1

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_det


set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap
theorem _root_.solution :
    dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2 = dot p p := F.gram_det
end TunnellMap
