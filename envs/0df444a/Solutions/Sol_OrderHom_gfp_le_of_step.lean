-- Prove2me | solution 1 for OrderHom.gfp_le_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:46:17.13709+00:00
-- url     : https://prove2.me/submissions/78129077-82b4-4aac-8bd2-0543b4f966b9

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.gfp ≤ a) (hb : b = f a) : f.gfp ≤ b := by
  subst hb
  calc f.gfp = f f.gfp := f.map_gfp.symm
    _ ≤ f a := f.monotone ha
end OrderHom
