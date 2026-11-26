-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:02.535077+00:00
-- url     : https://prove2.me/submissions/8d2d00ad-f626-4472-b601-2d4748dee820

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_eq_of_continuous
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_continuous

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace := by
  letI : TopologicalSpace E := scottTopologicalSpace
  intro X Y _ _ e he f
  exact ⟨⟨scottExtend e f, scottExtend_continuous hE e f⟩,
    fun x => scottExtend_eq_of_continuous hE e he f f.continuous x⟩
end Scott1972.ContinuousLattice
