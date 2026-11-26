-- Prove2me | solution 1 for Scott1972.ContinuousLattice.wayBelow_self_iff_scottOpen_Ici
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:29:03.07385+00:00
-- url     : https://prove2.me/submissions/96ce5d6a-7fda-4f4f-9926-85b4fe100f35

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {x : D} : x ≪ x ↔ ScottOpen (Set.Ici x) := by
  constructor
  · rintro ⟨U, hU, hxU, hsub⟩
    -- `Ici x = U`: `Ici x ⊆ U` since `U` is upper and `x ∈ U`; `U ⊆ Ici x` is `hsub`.
    have hIci : Set.Ici x = U :=
      le_antisymm (fun w hw => hU.1 (Set.mem_Ici.1 hw) hxU) hsub
    rw [hIci]; exact hU
  · intro hopen
    exact ⟨Set.Ici x, hopen, Set.self_mem_Ici, le_refl _⟩
end Scott1972.ContinuousLattice
