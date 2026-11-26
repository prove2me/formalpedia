-- Prove2me | solution 1 for Scott1972.ContinuousLattice.WayBelow.sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:29:26.402262+00:00
-- url     : https://prove2.me/submissions/ad53dcdb-dd14-47ed-863f-03c6022f6632

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_inter

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
namespace WayBelow
theorem _root_.solution {x y z : D} (hx : x ≪ z) (hy : y ≪ z) : x ⊔ y ≪ z := by
  obtain ⟨U, hU, hzU, hUsub⟩ := hx
  obtain ⟨V, hV, hzV, hVsub⟩ := hy
  refine ⟨U ∩ V, scottOpen_inter hU hV, ⟨hzU, hzV⟩, fun w hw => ?_⟩
  exact Set.mem_Ici.2 (sup_le (hUsub hw.1) (hVsub hw.2))
end WayBelow
end Scott1972.ContinuousLattice
