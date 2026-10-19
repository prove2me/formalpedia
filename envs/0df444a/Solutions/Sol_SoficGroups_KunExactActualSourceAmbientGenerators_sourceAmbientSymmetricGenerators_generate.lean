-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.sourceAmbientSymmetricGenerators_generate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/e443eb84-42ed-4b4e-80fe-200672b2f036

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sourceGeneratedGroup_eq_nine

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunExactKazhdanGeneratorChange
namespace SoficGroups.KunExactActualSourceAmbientGenerators
theorem _root_.solution
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hgeneratesΓ :
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤) :
    Subgroup.closure
      (sourceAmbientSymmetricGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) = ⊤ := by
  classical
  let K : Subgroup
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :=
    Subgroup.closure
      (sourceAmbientSymmetricGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode))
  have hpositive :
      ∀ x ∈ sourcePositiveGenerators SΓ, x ∈ K := by
    intro x hx
    apply Subgroup.subset_closure
    change x ∈ sourceAmbientSymmetricGenerators SΓ
    simp [sourceAmbientSymmetricGenerators, hx]
  have hcorner :
      ∀ g :
        SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode,
        sourceAlphaInclusion g ∈ K := by
    intro g
    have hsub :
        Subgroup.closure
          (SΓ : Set
            (SoficGroups.prefixElementaryGroup
              SoficGroups.alphaPrefixCode)) ≤
            K.comap sourceAlphaInclusion := by
      rw [Subgroup.closure_le]
      intro x hx
      change sourceAlphaInclusion x ∈ K
      apply hpositive
      change sourceAlphaInclusion x ∈
        SΓ.image sourceAlphaInclusion ∪
          {sourceCompressionU, sourceCompressionV}
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    apply hsub
    rw [hgeneratesΓ]
    simp
  let U : Subgroup SoficGroups.BinaryLeavittˣ :=
    K.map
      (SoficGroups.prefixElementaryGroup
        SoficGroups.ninePrefixCode).subtype
  have hsource :
      SoficGroups.SourceGeneration.sourceGeneratedGroup ≤ U := by
    rw [SoficGroups.SourceGeneration.sourceGeneratedGroup,
      Subgroup.closure_le]
    intro x hx
    rcases hx with hα | htables
    · let a :
          SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode := ⟨x, hα⟩
      exact ⟨sourceAlphaInclusion a, hcorner a, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htables
      rcases htables with rfl | rfl
      · exact ⟨sourceCompressionU,
          hpositive sourceCompressionU
            (by simp [sourcePositiveGenerators]), rfl⟩
      · exact ⟨sourceCompressionV,
          hpositive sourceCompressionV
            (by simp [sourcePositiveGenerators]), rfl⟩
  have htop :
      (⊤ : Subgroup
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) ≤ K := by
    intro x _hx
    have hxin :
        (x.val : SoficGroups.BinaryLeavittˣ) ∈
          SoficGroups.SourceGeneration.sourceGeneratedGroup := by
      rw [SoficGroups.sourceGeneratedGroup_eq_nine]
      exact x.property
    obtain ⟨y, hy, hval⟩ := hsource hxin
    have heq : y = x := by
      apply Subtype.ext
      exact hval
    simpa [← heq] using hy
  exact top_unique htop
end SoficGroups.KunExactActualSourceAmbientGenerators
