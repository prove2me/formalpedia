-- Prove2me | solution 1 for Scott1972.ContinuousLattice.wayBelow_sSup_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:50.588934+00:00
-- url     : https://prove2.me/submissions/2f35827c-12d0-4f82-9405-01af66e91f94

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
theorem _root_.solution {x : D} {S : Set D} (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : x ≪ sSup S ↔ ∃ y ∈ S, x ≪ y := by
  constructor
  · rintro ⟨U, hU, hsupU, hsub⟩
    obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
    exact ⟨s, hsS, U, hU, hsU, hsub⟩
  · rintro ⟨y, hyS, hxy⟩
    exact hxy.trans_le (le_sSup hyS)
end Scott1972.ContinuousLattice
