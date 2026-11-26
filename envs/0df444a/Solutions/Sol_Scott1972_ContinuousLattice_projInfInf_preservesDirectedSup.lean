-- Prove2me | solution 1 for Scott1972.ContinuousLattice.projInfInf_preservesDirectedSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:01.149273+00:00
-- url     : https://prove2.me/submissions/fd05c0b3-1aae-4906-ab30-b3f4f058a012

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_5


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    PreservesDirectedSup (projInfInf D₀ j₀ : DInfFn D₀ j₀ → DInf D₀ j₀) :=
  (proposition_2_5 _).mp (projInfInf D₀ j₀).continuous
end Scott1972.ContinuousLattice
