-- Prove2me | solution 1 for Scott1972.ContinuousLattice.WayBelow.le_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:19.237921+00:00
-- url     : https://prove2.me/submissions/a95dc1f0-db77-43f0-8f01-bf64850218ce

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
namespace WayBelow
theorem _root_.solution {x y z : D} (hxy : x ≤ y) (h : y ≪ z) : x ≪ z := by
  obtain ⟨U, hU, hzU, hsub⟩ := h
  refine ⟨U, hU, hzU, fun w hw => ?_⟩
  have hyw : y ≤ w := Set.mem_Ici.1 (hsub hw)
  exact Set.mem_Ici.2 (hxy.trans hyw)
end WayBelow
end Scott1972.ContinuousLattice
