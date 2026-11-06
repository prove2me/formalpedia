-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_forward_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:28:58.277035+00:00
-- url     : https://prove2.me/submissions/c96fac08-7756-4175-8ed5-92031be8bad4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicRationalProjection_normalizedRefinement


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : GlobalPlace F256 E) (x y : E) (hx : Transcendental F256 x)
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    (h : y ^ 16 + y = sourceStepRhs x) :
    PlaceNormalizedExtension Q F256⟮x⟯ (F256⟮x⟯ ⊔ F256⟮y⟯) := by
  refine ⟨le_sup_left, ?_⟩
  have hc := sourceBasicRationalProjection_normalizedRefinement x hx y
    (AmbientPlaceModels.baseRing F256⟮x⟯ Q) (AmbientPlaceModels.prime F256⟮x⟯ Q) h
  have heq : (F256⟮x⟯)⟮y⟯ =
      IntermediateField.extendScalars (show F256⟮x⟯ ≤ F256⟮x⟯ ⊔ F256⟮y⟯ from le_sup_left) := by
    apply IntermediateField.restrictScalars_injective F256
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    rfl
  rwa [heq] at hc
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
