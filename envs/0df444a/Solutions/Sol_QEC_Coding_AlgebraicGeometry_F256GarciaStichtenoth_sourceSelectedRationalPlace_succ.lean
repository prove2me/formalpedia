-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:48:31.551203+00:00
-- url     : https://prove2.me/submissions/858c4ed2-7e8d-44d2-8efc-ec6dba357766

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (index : SourceSelectedPlaceIndex i)
    (c : LinearMap.ker f256ArtinSchreier) :
    sourceSelectedRationalPlace (i + 1) (index, c) =
      sourceSplitUpperRationalPlace (sourceSelectedRationalPlace i index)
        (sourceDistinguishedPlace i) (sourceDistinguishedCoordinate i)
        (sourceDistinguishedCoordinate_order i)
        (sourceSelectedRationalPlace_coordinate_regular i index)
        (sourceSelectedPlaceData i index).coordinate_split c := by
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
