-- Prove2me | solution 1 for Scott1972.ContinuousLattice.towerProj_succ_incl_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:01.495899+00:00
-- url     : https://prove2.me/submissions/bf904773-5c08-4e68-b099-73949d0efd57

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (n : ℕ) (x : towerType D₀ (n + 1)) (y : towerType D₀ (n + 1)) :
    ((towerProj D₀ j₀ (n + 1)).incl x) y
      = (towerProj D₀ j₀ n).incl (x ((towerProj D₀ j₀ n).retr y)) := rfl
end Scott1972.ContinuousLattice
