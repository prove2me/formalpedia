-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kification_isEmbedding_of_range_isKSpace
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:24:56.123888+00:00
-- url     : https://prove2.me/submissions/8eff21d0-e271-41f0-bffe-d6d9ff1e5ed7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.Topology.Homeomorph.Lemmas
noncomputable section
universe u
open CategoryTheory Topology TopologicalSpace Set
namespace QAlgorithms.Papers.Independent.Intakethird100.P07
end QAlgorithms.Papers.Independent.Intakethird100.P07

open QAlgorithms.Papers.Independent.Intakethird100.P07

theorem solution
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsEmbedding f)
    (hR : UCompactlyGeneratedSpace.{u} {y : KSpace Y // y ∈ Set.range f}) :
    @IsEmbedding (KSpace X) (KSpace Y) _ _ f := by
  classical
  let R := {y : KSpace Y // y ∈ Set.range f}
  letI : UCompactlyGeneratedSpace.{u} R := hR
  let e := hf.toHomeomorph
  let g : C(R,X) := ⟨fun y => e.symm ⟨y.val,y.property⟩,
    e.symm.continuous.comp (((kToOriginal (ContinuousMap.id Y)).continuous.comp
      continuous_subtype_val).subtype_mk (fun y => y.property))⟩
  have hg : @Continuous R (KSpace X) inferInstance (kSpaceTopology X) (fun y : R => g y) :=
    continuous_from_uCompactlyGeneratedSpace (X := R) (Y := KSpace X) g
      (fun S q => (kProbe S (g.comp q)).continuous)
  let E : KSpace X ≃ₜ R := {
    toFun := fun x => ⟨f x,⟨x,rfl⟩⟩
    invFun := fun y => g y
    left_inv := by intro x; exact e.symm_apply_apply x
    right_inv := by
      intro y
      apply Subtype.ext
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y.val,y.property⟩)
    continuous_toFun := (kMap (⟨f,hf.continuous⟩ : C(X,Y))).continuous.subtype_mk _
    continuous_invFun := hg }
  exact IsEmbedding.subtypeVal.comp E.isEmbedding
