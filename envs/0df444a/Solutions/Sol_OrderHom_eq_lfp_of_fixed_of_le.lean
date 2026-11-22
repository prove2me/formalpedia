-- Prove2me | solution 1 for OrderHom.eq_lfp_of_fixed_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:45:36.984669+00:00
-- url     : https://prove2.me/submissions/cdf8f370-6b88-4512-a543-7bab6b5f11d3

import Mathlib.Order.FixedPoints
import Definitions.Def_Comp_Lattice

set_option autoImplicit true

namespace OrderHom
theorem _root_.solution {α : Type*} [CompleteLattice α] (f : α →o α) {a : α}
    (hfix : f a = a) (hle : a ≤ f.lfp) : a = f.lfp :=
  le_antisymm hle (f.lfp_le hfix.le)
end OrderHom
