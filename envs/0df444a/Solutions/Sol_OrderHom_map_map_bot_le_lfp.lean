-- Prove2me | solution 1 for OrderHom.map_map_bot_le_lfp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:55:20.852744+00:00
-- url     : https://prove2.me/submissions/1868a152-ec41-4aad-b47d-81bca2c3d618

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) :
    f (f ⊥) ≤ f.lfp := by
  have h1 : f ⊥ ≤ f.lfp := by
    calc f ⊥ ≤ f f.lfp := f.mono bot_le
      _ = f.lfp := f.map_lfp
  calc f (f ⊥) ≤ f f.lfp := f.mono h1
    _ = f.lfp := f.map_lfp
end OrderHom
