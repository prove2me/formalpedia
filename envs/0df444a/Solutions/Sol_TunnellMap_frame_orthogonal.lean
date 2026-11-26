-- Prove2me | solution 1 for TunnellMap.frame_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:02.494354+00:00
-- url     : https://prove2.me/submissions/155d59fb-8a52-4c89-aaa0-b7bae4928a44

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
import Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a
import Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3


set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap
theorem _root_.solution : dot p F.e₁ = 0 ∧ dot p F.e₂ = 0 :=
  ⟨F.e₁_orthogonal, F.e₂_orthogonal⟩
end TunnellMap
