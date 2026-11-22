-- Prove2me | solution 1 for OrderHom.lfp_le_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:59:47.457804+00:00
-- url     : https://prove2.me/submissions/0e04c467-c30c-41ba-803c-0caf79e93f05

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) {a b : α}
    (ha : f.lfp ≤ a) (hb : b = f a) : f.lfp ≤ b := by
  subst hb
  calc f.lfp = f f.lfp := f.map_lfp.symm
    _ ≤ f a := f.monotone ha
end OrderHom
