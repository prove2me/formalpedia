-- Prove2me | solution 1 for Scott1972.ContinuousLattice.isContinuousLattice_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:25.816851+00:00
-- url     : https://prove2.me/submissions/7608517f-586a-4bfe-99b7-69e42986e7da

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_8

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution : IsContinuousLattice Prop :=
  proposition_2_8
end Scott1972.ContinuousLattice
