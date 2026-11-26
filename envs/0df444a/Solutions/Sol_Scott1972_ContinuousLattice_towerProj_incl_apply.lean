-- Prove2me | solution 1 for Scott1972.ContinuousLattice.towerProj_incl_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:52.145964+00:00
-- url     : https://prove2.me/submissions/79fd46a1-d8dd-46cd-ab3d-9753a0fd1bd0

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
import Theorems.Thm_Scott1972_ContinuousLattice_towerProj_succ_incl_apply

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (n : ℕ) (f : towerType D₀ (n + 1)) (x : towerType D₀ n) :
    (towerProj D₀ j₀ n).incl (f x)
      = ((towerProj D₀ j₀ (n + 1)).incl f) ((towerProj D₀ j₀ n).incl x) := by
  rw [towerProj_succ_incl_apply, (towerProj D₀ j₀ n).retr_incl]
end Scott1972.ContinuousLattice
