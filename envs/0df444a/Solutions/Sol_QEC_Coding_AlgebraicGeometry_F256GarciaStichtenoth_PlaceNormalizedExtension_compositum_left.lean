-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedExtension.compositum_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:00.527797+00:00
-- url     : https://prove2.me/submissions/0e6bf1d6-7c07-4ec4-ab03-9304066cf1d4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_restrictScalars_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_compositum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_compositum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_compositum


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
variable (Q : GlobalPlace F256 E) {K L M : IntermediateField F256 E}
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace PlaceNormalizedExtension
theorem _root_.solution [Finite Q.residueField]
    (hL : PlaceNormalizedExtension Q K L) (hM : PlaceNormalizedExtension Q K M) :
    PlaceNormalizedExtension Q L (L ⊔ M) := by
  obtain ⟨hKL, hL⟩ := hL
  obtain ⟨hKM, hM⟩ := hM
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  let LK : IntermediateField K E := IntermediateField.extendScalars hKL
  let MK : IntermediateField K E := IntermediateField.extendScalars hKM
  have h := (PlaceNormalizedRefinement.compositum Q hL hM).1
  refine ⟨le_sup_left, ?_⟩
  apply (PlaceNormalizedRefinement.restrictScalars_iff K L Q).mpr
  have hbot : (⊥ : IntermediateField L E).restrictScalars K = LK :=
    IntermediateField.restrictScalars_bot_eq_self LK
  have htop : (IntermediateField.extendScalars (show L ≤ L ⊔ M from le_sup_left)).restrictScalars K =
      LK ⊔ MK := by
    apply IntermediateField.restrictScalars_injective F256
    change L ⊔ M = (LK ⊔ MK).restrictScalars F256
    rw [← IntermediateField.restrictScalars_sup]
    rfl
  rwa [hbot, htop]
end PlaceNormalizedExtension
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
