-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:16.978611+00:00
-- url     : https://prove2.me/submissions/3c2b6a2b-97ef-4862-a758-f070611cee47

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r)
    (hdiag : BuildingElementHasIdentityConjugationDiagonal P r g) :
    g = 1 := by
  obtain ⟨u, j, hj, hgForm⟩ :=
    exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup P r g hg
  have hnormalDiag := hdiag u j hj hgForm
  rw [hgForm]
  exact buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
    P r u j hj hnormalDiag
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
