-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottOpen_wayBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:54.961542+00:00
-- url     : https://prove2.me/submissions/f04012ea-4533-4408-9836-a71336b2a388

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_trans_le

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (x : D) : ScottOpen {z | x ≪ z} := by
  refine ⟨fun a b hab ha => ha.trans_le hab, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩
end Scott1972.ContinuousLattice
