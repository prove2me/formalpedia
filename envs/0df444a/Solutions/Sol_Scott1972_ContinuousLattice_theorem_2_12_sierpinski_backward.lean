-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_2_12_sierpinski_backward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:42.769903+00:00
-- url     : https://prove2.me/submissions/00149144-0117-49be-aceb-443df9d0a965

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_proposition_1_2


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (_h : IsContinuousLattice Prop) : IsInjectiveSpace Prop :=
  proposition_1_2
end Scott1972.ContinuousLattice
