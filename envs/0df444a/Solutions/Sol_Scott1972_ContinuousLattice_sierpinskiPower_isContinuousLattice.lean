-- Prove2me | solution 1 for Scott1972.ContinuousLattice.sierpinskiPower_isContinuousLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:05.318776+00:00
-- url     : https://prove2.me/submissions/e88f9953-ce7a-4af9-8985-d5c07ab0eeba

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_9_a
import Theorems.Thm_Scott1972_ContinuousLattice_isContinuousLattice_prop

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (ι : Type*) : IsContinuousLattice (ι → Prop) :=
  proposition_2_9_a (fun _ => Prop) (fun _ => isContinuousLattice_prop)
end Scott1972.ContinuousLattice
