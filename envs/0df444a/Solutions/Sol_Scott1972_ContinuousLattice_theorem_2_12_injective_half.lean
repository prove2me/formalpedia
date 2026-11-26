-- Prove2me | solution 1 for Scott1972.ContinuousLattice.theorem_2_12_injective_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:44.698818+00:00
-- url     : https://prove2.me/submissions/c45fa7ee-7a34-4a25-820a-b3dbb3daef1b

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
theorem _root_.solution : IsInjectiveSpace Prop :=
  proposition_1_2
end Scott1972.ContinuousLattice
