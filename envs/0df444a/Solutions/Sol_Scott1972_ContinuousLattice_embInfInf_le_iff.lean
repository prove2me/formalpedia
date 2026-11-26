-- Prove2me | solution 1 for Scott1972.ContinuousLattice.embInfInf_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:13.572823+00:00
-- url     : https://prove2.me/submissions/da31ca4e-f35d-47af-8ab6-48f3ec678017

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
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (x y : DInf D₀ j₀) :
    embInfInf D₀ j₀ x ≤ embInfInf D₀ j₀ y ↔ x ≤ y := by
  constructor
  · intro h
    have := (projInfInf D₀ j₀).monotone h
    rwa [projInfInf_embInfInf, projInfInf_embInfInf] at this
  · intro h; exact (embInfInf D₀ j₀).monotone h
end Scott1972.ContinuousLattice
