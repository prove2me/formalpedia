-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinates_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:50.123844+00:00
-- url     : https://prove2.me/submissions/fd664897-9c74-47a7-92bc-8f0a08c2195e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceCoordinates_window_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalCoordinateWindow_normalized


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) (Q : GlobalPlace F256 (SourceField m)) :
    PlaceNormalizedExtension Q F256⟮sourceCoordinates m 0⟯ ⊤ := by
  letI : Algebra (Polynomial F256) (SourceField m) :=
    ((algebraMap (RatFunc F256) (SourceField m)).comp
      (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
  letI : IsScalarTower (Polynomial F256) (RatFunc F256) (SourceField m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Finite Q.residueField := GlobalPlace.finite_residueField Q
  have h := rationalCoordinateWindow_normalized Q (sourceCoordinates m)
    (sourceCoordinates_transcendental m) m (sourceCoordinates_recursion m)
  rwa [sourceCoordinates_window_eq_top] at h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
