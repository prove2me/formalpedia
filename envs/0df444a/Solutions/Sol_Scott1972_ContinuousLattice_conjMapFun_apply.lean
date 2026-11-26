-- Prove2me | solution 1 for Scott1972.ContinuousLattice.conjMapFun_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:44.876065+00:00
-- url     : https://prove2.me/submissions/fff89c8c-fd1c-45ee-90c8-f588e9d9a2e7

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
open Set
variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) (x : W) :
    conjMapFun post pre f x = post (f (pre x)) := rfl
end Scott1972.ContinuousLattice
