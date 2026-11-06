-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedPlace_residueDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:15:38.498743+00:00
-- url     : https://prove2.me/submissions/2cb0efdf-946f-434d-a969-de63a24c0964

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_globalResidueDegree_eq_one


set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) (j : Fin (selectedLength i)) :
    GlobalPlace.residueDegree (selectedPlace i j) = 1 := by
  exact RationalPlace.globalResidueDegree_eq_one
    (selectedRationalPlaceAt i j)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
