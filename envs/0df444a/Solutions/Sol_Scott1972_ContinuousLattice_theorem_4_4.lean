-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:17.440683+00:00
-- url     : https://prove2.me/submissions/a149c2a6-73d7-498c-a095-c6c4060c4a71

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_4_1
import Theorems.Thm_Scott1972_ContinuousLattice_theorem_3_3_isContinuousLattice


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (h₀ : IsContinuousLattice D₀.carrier) :
    @IsContinuousLattice (DInf D₀ j₀) inferInstance ∧
      Nonempty
        (@Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
          (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
          (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀))) := by
  have hTower : ∀ n, IsContinuousLattice (towerType D₀ n) := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih => exact theorem_3_3_isContinuousLattice ih ih
  refine ⟨proposition_4_1 (towerType D₀) (towerProj D₀ j₀) hTower, ?_⟩
  exact ⟨theorem_4_4_sourceTopology_homeomorph D₀ j₀ hTower⟩
end Scott1972.ContinuousLattice
