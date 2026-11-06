-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlaceAt_evaluate_baseCoordinate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:22.416938+00:00
-- url     : https://prove2.me/submissions/5603fa94-2ba1-40b7-a4e5-d9040cefa499

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fintype
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedRationalPlace_evaluate_baseCoordinate_ne_zero


set_option autoImplicit false
open Filter
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (j : Fin (selectedLength i)) :
    (selectedRationalPlaceAt i j).evaluateRegular
        (baseCoordinate (i + 2))
        (selectedRationalPlaceAt_baseCoordinate_regular i j) ≠ 0 :=
  selectedRationalPlace_evaluate_baseCoordinate_ne_zero
    (i + 2) (selectedPlaceIndexEquiv i j)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
