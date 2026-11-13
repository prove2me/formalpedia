-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kification_coreflection
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T22:56:44.625509+00:00
-- url     : https://prove2.me/submissions/d91f9b0a-5576-4f05-80db-4a3e40dfadfc

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Proposition B.5, PDF p. 36: the specified k functor is right adjoint
to the fully faithful inclusion of compactly generated spaces. -/
theorem solution :
    Nonempty (CompactlyGenerated.compactlyGeneratedToTop.{u, u} ⊣
      kCoreflector.{u}) := by
  classical
  refine ⟨CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => CompactlyGenerated.ofHom ⟨f.hom, ?_⟩
      invFun := fun g => TopCat.ofHom ⟨g.hom, ?_⟩
      left_inv := by intro f; ext x; rfl
      right_inv := by intro g; ext x; rfl }
    homEquiv_naturality_left_symm := by intros; ext x; rfl
    homEquiv_naturality_right := by intros; ext x; rfl }⟩
  · exact continuous_from_uCompactlyGeneratedSpace (X := X) (Y := KSpace Y) f.hom
      (fun S g => (kProbe S (f.hom.comp g)).continuous)
  · exact (kToOriginal (ContinuousMap.id Y)).continuous.comp g.hom.hom.continuous
