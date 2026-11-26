-- Prove2me | solution 1 for Scott1972.ContinuousLattice.towerType_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:41.423727+00:00
-- url     : https://prove2.me/submissions/29289883-c14e-4229-93d6-1c0e9f93c865

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
namespace Scott1972.ContinuousLattice
theorem _root_.solution (D₀ : CLat.{u}) (n : ℕ) :
    towerType D₀ (n + 1) = ScottMap (towerType D₀ n) (towerType D₀ n) := rfl
end Scott1972.ContinuousLattice
