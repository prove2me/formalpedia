-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMapOfLE_strictTransform__a3eda6dd338c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:26:12.82385+00:00
-- url     : https://prove2.me/submissions/99275061-eef9-4854-994c-7b94bd0789b2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprod_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedCoprod_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_inducedBlowups_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedResolutionRule_toAffineResolutionRule_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformMap_comp_strictTransform__e57863292142
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprod_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedCoprod_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.inducedBlowups_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.EmbeddedResolutionRule.toAffineResolutionRule_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)
private theorem strictTransformMapOfLE_succ_of_le (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.strictTransformMapOfLE h' = T.strictTransformMap b ≫ T.strictTransformMapOfLE h := by
  exact Nat.leRec_succ ..
end EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)
namespace FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
theorem _root_.solution {a b : ℕ} (h : a ≤ b) :
    S.strictTransformMapOfLE h ≫ S.strictTransformι a = S.strictTransformι b ≫ S.ambientSeq.transitionMap h := by
  induction b, h using Nat.le_induction with
  | base =>
      have e1 : S.strictTransformMapOfLE (Nat.le_refl a) = 𝟙 (S.strictTransform a) := by
        simp [EmbeddedBlowupSequence.strictTransformMapOfLE, Nat.leRec_self]
      have e2 : S.ambientSeq.transitionMap (Nat.le_refl a) = 𝟙 (S.ambientSeq.schemeAt a) := by
        simp [SequenceOfBlowups.transitionMap_def]
      simp only [e1, e2, Category.id_comp, Category.comp_id]
  | succ b hb ih =>
      have e1 : S.strictTransformMapOfLE (Nat.le_succ_of_le hb) = S.strictTransformMap b ≫ S.strictTransformMapOfLE hb :=
        strictTransformMapOfLE_succ_of_le S hb
      have e2 : S.ambientSeq.transitionMap (Nat.le_succ_of_le hb)
          = S.ambientSeq.transitionMapSucc b ≫ S.ambientSeq.transitionMap hb := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact (SequenceOfBlowups.transitionMap_trans S.ambientSeq hb (Nat.le_succ b)).symm
      have e3 : S.strictTransformMap b ≫ S.strictTransformι b
          = S.strictTransformι (b + 1) ≫ S.ambientSeq.transitionMapSucc b := S.strictTransformMap_comp_strictTransformι b
      rw [e1, e2, Category.assoc, ih, ← Category.assoc, e3]
      simp only [Category.assoc]
end FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
