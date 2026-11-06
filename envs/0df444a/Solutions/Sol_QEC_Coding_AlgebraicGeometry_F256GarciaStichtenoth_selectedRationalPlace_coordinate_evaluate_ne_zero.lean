-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_coordinate_evaluate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:08.389992+00:00
-- url     : https://prove2.me/submissions/2adf043d-2cc0-491f-a2e0-a5a74bda819d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (index : SelectedPlaceIndex i) :
    (selectedRationalPlace i index).evaluateRegular
        (distinguishedCoordinate i)
        (selectedRationalPlace_coordinate_regular i index) ≠ 0 :=
  (selectedPlaceData i index).coordinate_evaluate_ne_zero
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
