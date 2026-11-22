-- Prove2me | solution 1 for OrderHom.eq_gfp_of_fixed_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:46:06.229046+00:00
-- url     : https://prove2.me/submissions/5a3ad130-e70d-4a82-a36c-9ef51b871051

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hge : f.gfp ≤ a) : a = f.gfp :=
  le_antisymm (f.le_gfp hfix.ge) hge
end OrderHom
