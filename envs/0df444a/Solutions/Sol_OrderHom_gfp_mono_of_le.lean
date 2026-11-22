-- Prove2me | solution 1 for OrderHom.gfp_mono_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:52:42.898147+00:00
-- url     : https://prove2.me/submissions/3cda5c6c-9264-4322-87a9-8a0020730dfa

import Definitions.Def_Csg_CsgMonotone
import Definitions.Def_Csg_BuchiOp

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] {f g : α →o α}
    (h : ∀ a, f a ≤ g a) : f.gfp ≤ g.gfp :=
  g.le_gfp ((le_of_eq f.map_gfp.symm).trans (h f.gfp))
end OrderHom
