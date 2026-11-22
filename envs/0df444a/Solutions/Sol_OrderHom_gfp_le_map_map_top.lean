-- Prove2me | solution 1 for OrderHom.gfp_le_map_map_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:02:59.586882+00:00
-- url     : https://prove2.me/submissions/ba086c62-36ac-489f-b1df-8db1f29375c9

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) :
    f.gfp ≤ f (f ⊤) := by
  have h1 : f.gfp ≤ f ⊤ := by
    calc f.gfp = f f.gfp := f.map_gfp.symm
      _ ≤ f ⊤ := f.mono le_top
  calc f.gfp = f f.gfp := f.map_gfp.symm
    _ ≤ f (f ⊤) := f.mono h1
end OrderHom
