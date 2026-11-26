-- Prove2me | solution 1 for Scott1972.ContinuousLattice.bot_wayBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:29:26.941139+00:00
-- url     : https://prove2.me/submissions/49542c17-8ab7-43f2-bf4e-2e809b12ee02

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_univ

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (x : D) : (⊥ : D) ≪ x :=
  ⟨Set.univ, scottOpen_univ, Set.mem_univ x, fun _ _ => bot_le⟩
end Scott1972.ContinuousLattice
