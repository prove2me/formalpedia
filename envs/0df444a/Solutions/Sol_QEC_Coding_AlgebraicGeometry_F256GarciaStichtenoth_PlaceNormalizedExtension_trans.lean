-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedExtension.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:27:45.477756+00:00
-- url     : https://prove2.me/submissions/f8f9fafb-72de-49f5-87d5-b91a163b1862

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_restrictScalars_iff

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
theorem _root_.solution
    (hKL : PlaceNormalizedExtension Q K L) (hLM : PlaceNormalizedExtension Q L M) :
    PlaceNormalizedExtension Q K M := by
  obtain ⟨hleKL, hKL⟩ := hKL
  obtain ⟨hleLM, hLM⟩ := hLM
  letI : Algebra K L := (IntermediateField.inclusion hleKL).toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  let LK : IntermediateField K E := IntermediateField.extendScalars hleKL
  have h := (PlaceNormalizedRefinement.restrictScalars_iff K L Q).mp hLM
  have hbot : (⊥ : IntermediateField L E).restrictScalars K = LK :=
    IntermediateField.restrictScalars_bot_eq_self LK
  have htop : (IntermediateField.extendScalars hleLM).restrictScalars K =
      IntermediateField.extendScalars (hleKL.trans hleLM) := rfl
  rw [hbot, htop] at h
  exact ⟨hleKL.trans hleLM, hKL.trans h⟩
end PlaceNormalizedExtension
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
