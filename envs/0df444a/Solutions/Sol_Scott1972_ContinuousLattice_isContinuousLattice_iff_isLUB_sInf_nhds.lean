-- Prove2me | solution 1 for Scott1972.ContinuousLattice.isContinuousLattice_iff_isLUB_sInf_nhds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:06.24781+00:00
-- url     : https://prove2.me/submissions/0803c087-97f5-4408-9e5c-e1ef67b431fe

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_sInf_wayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    IsContinuousLattice D ↔
      ∀ y : D, IsLUB {a : D | ∃ U, ScottOpen U ∧ y ∈ U ∧ a = sInf U} y := by
  constructor
  · intro h y
    refine ⟨?_, ?_⟩
    · rintro a ⟨U, hU, hyU, rfl⟩
      exact (sInf_wayBelow hU hyU).le
    · intro b hb
      refine (h y).2 ?_
      intro x hx
      obtain ⟨U, hU, hyU, hsub⟩ := hx
      have hxle : x ≤ sInf U := le_sInf fun _ hz => Set.mem_Ici.1 (hsub hz)
      exact hxle.trans (hb ⟨U, hU, hyU, rfl⟩)
  · intro h y
    refine ⟨fun x hx => hx.le, ?_⟩
    intro b hb
    refine (h y).2 ?_
    rintro a ⟨U, hU, hyU, rfl⟩
    exact hb (sInf_wayBelow hU hyU)
end Scott1972.ContinuousLattice
