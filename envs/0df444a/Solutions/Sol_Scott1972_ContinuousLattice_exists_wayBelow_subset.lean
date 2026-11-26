-- Prove2me | solution 1 for Scott1972.ContinuousLattice.exists_wayBelow_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:30:22.350645+00:00
-- url     : https://prove2.me/submissions/36e9968f-0c1d-4a0f-8cd0-079ab6d495c4

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_bot_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_sSup_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_directedOn_wayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ {w | a ≪ w} ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 hw.le haU⟩
end Scott1972.ContinuousLattice
