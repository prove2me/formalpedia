-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.BuildingCompactCyclicSubgroup_le_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:18.024265+00:00
-- url     : https://prove2.me/submissions/720b9316-ee08-4779-82e3-dc70b08d7fda

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGenerator_mem_maximalCompact


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    BuildingCompactCyclicSubgroup P r ≤
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  rw [BuildingCompactCyclicSubgroup]
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | hg)
  · obtain ⟨u, rfl⟩ := hg
    exact buildingConstant_mem_maximalCompact P r u
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact buildingCyclicGenerator_mem_maximalCompact P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
