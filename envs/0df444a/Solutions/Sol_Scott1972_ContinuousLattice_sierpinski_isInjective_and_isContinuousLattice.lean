-- Prove2me | solution 1 for Scott1972.ContinuousLattice.sierpinski_isInjective_and_isContinuousLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:58.115845+00:00
-- url     : https://prove2.me/submissions/7bd60bac-9387-45fc-a218-699b79c28d9f

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_isContinuousLattice_prop
import Theorems.Thm_proposition_1_2


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    IsInjectiveSpace Prop ∧ IsContinuousLattice Prop :=
  ⟨proposition_1_2, isContinuousLattice_prop⟩
end Scott1972.ContinuousLattice
