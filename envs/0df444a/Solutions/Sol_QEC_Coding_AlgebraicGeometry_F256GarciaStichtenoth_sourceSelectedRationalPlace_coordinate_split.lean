-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_coordinate_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:47:12.921201+00:00
-- url     : https://prove2.me/submissions/1ae57664-a0ad-44ef-9eb1-3a6a545b8fe4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (index : SourceSelectedPlaceIndex i) :
    galoisBaseWValue
        ((sourceSelectedRationalPlace i index).evaluateRegular
          (sourceDistinguishedCoordinate i)
          (sourceSelectedRationalPlace_coordinate_regular i index)) ≠ 0 :=
  (sourceSelectedPlaceData i index).coordinate_split
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
