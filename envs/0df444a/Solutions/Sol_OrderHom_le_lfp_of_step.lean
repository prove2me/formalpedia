-- Prove2me | solution 1 for OrderHom.le_lfp_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:25.877371+00:00
-- url     : https://prove2.me/submissions/215d149a-bb10-479a-9f5e-b905dc67ac07

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : a ≤ f.lfp) (hb : b = f a) : b ≤ f.lfp := by
  subst hb
  calc f a ≤ f f.lfp := f.monotone ha
    _ = f.lfp := f.map_lfp
end OrderHom
