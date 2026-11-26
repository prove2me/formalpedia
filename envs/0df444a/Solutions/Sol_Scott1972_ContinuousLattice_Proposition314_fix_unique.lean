-- Prove2me | solution 1 for Scott1972.ContinuousLattice.Proposition314.fix_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:14.306261+00:00
-- url     : https://prove2.me/submissions/46849637-151d-48bc-b07d-49db6755995a

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Scott1972.ContinuousLattice.Proposition314
namespace Scott1972.ContinuousLattice.Proposition314
theorem _root_.solution {f : ScottMap D D} {a : D} (hfix : (f : D → D) a = a)
    (hleast : ∀ x, (f : D → D) x ≤ x → a ≤ x) : a = fix f :=
  le_antisymm (hleast (fix f) (le_of_eq (fix_eq f))) (fix_le hfix.le)
end Scott1972.ContinuousLattice.Proposition314
