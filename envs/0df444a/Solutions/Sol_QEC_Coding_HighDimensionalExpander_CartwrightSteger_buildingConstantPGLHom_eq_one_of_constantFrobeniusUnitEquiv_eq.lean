-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGLHom_eq_one_of_constantFrobeniusUnitEquiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:20:43.963788+00:00
-- url     : https://prove2.me/submissions/eb6c5247-5521-43c4-8582-dede778ad477

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_baseUnit_of_constantFrobeniusUnitEquiv_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingConstantPGLHom_map_baseUnit_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (hu : constantFrobeniusUnitEquiv P r u = u) :
    buildingConstantPGLHom P r u = 1 := by
  obtain ⟨a, rfl⟩ :=
    exists_baseUnit_of_constantFrobeniusUnitEquiv_eq P r u hu
  exact buildingConstantPGLHom_map_baseUnit_eq_one P r a
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
