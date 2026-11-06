-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedRationalPlace_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:07.623658+00:00
-- url     : https://prove2.me/submissions/0fb61a7b-f1fb-42a5-b612-d90ec6a8b907

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedPlaces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (index : SelectedPlaceIndex i)
    (c : LinearMap.ker f256ArtinSchreier) :
    selectedRationalPlace (i + 1) (index, c) =
      splitUpperRationalPlace (selectedRationalPlace i index)
        (distinguishedPlace i) (distinguishedCoordinate i)
        (distinguishedCoordinate_order i)
        (selectedRationalPlace_coordinate_regular i index) c := by
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
