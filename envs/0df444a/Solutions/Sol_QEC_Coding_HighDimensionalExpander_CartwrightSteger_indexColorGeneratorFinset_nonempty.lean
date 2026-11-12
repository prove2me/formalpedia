-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColorGeneratorFinset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:26:31.473503+00:00
-- url     : https://prove2.me/submissions/16a9e2ba-8c55-44ed-af7d-bc5fb0703b7f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingRelationTupleFinset_nonempty

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level k : Nat) :
    (indexColorGeneratorFinset P r level k).Nonempty := by
  obtain ⟨u, hu⟩ := buildingRelationTupleFinset_nonempty P r
  refine ⟨indexGeneratorPrefixProduct P r level k u, ?_⟩
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
