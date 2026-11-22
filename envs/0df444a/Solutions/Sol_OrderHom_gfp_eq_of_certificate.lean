-- Prove2me | solution 1 for OrderHom.gfp_eq_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:09:13.559347+00:00
-- url     : https://prove2.me/submissions/99de5c4a-f85b-4379-88ff-237fa346eb87

import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_SafetyCertificate

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hub : ∀ b, b ≤ f b → b ≤ v) : f.gfp = v :=
  le_antisymm (f.gfp_le hub) (f.le_gfp hfixed.ge)
end OrderHom
