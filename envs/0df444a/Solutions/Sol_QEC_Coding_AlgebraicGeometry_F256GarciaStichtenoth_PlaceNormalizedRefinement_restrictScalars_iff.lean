-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.restrictScalars_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:48.228689+00:00
-- url     : https://prove2.me/submissions/16918f5e-da81-4c09-a8be-ce3ca28c985c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AmbientPlaceModels_prime_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_of_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_of_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_restrictScalars_of_common_ambient_order


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
variable (F K : Type*) [_root_.Field F] [_root_.Field K]
    [Algebra F256 F] [Algebra F256 K] [Algebra F K] [Algebra K E] [Algebra F E]
    [IsScalarTower F K E] [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (Q : GlobalPlace F256 E)
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace PlaceNormalizedRefinement
theorem _root_.solution
    {J L : IntermediateField K E} :
    PlaceNormalizedRefinement K Q J L ↔
      PlaceNormalizedRefinement F Q (J.restrictScalars F) (L.restrictScalars F) := by
  let A := AmbientPlaceModels.baseRing F Q
  let B := AmbientPlaceModels.baseRing K Q
  let QA := AmbientPlaceModels.prime F Q
  let QB := AmbientPlaceModels.prime K Q
  have hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order :=
    (AmbientPlaceModels.prime_order F Q).trans (AmbientPlaceModels.prime_order K Q).symm
  exact ⟨fun h => h.restrictScalars_of_common_ambient_order A B F K E QA QB hupper,
    fun h => h.of_restrictScalars_of_common_ambient_order A B F K E QA QB hupper⟩
end PlaceNormalizedRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
