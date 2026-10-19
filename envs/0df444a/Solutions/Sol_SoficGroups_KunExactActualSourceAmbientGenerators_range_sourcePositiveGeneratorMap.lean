-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.range_sourcePositiveGeneratorMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/520ed92c-71e1-45fd-a1ec-f2bf13fcc289

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
namespace SoficGroups.KunExactActualSourceAmbientGenerators
theorem _root_.solution
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Set.range (sourcePositiveGeneratorMap SΓ) =
      (sourcePositiveGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with i | i
    · change
        sourceAlphaInclusion
          (i :
            SoficGroups.prefixElementaryGroup
              SoficGroups.alphaPrefixCode) ∈
            sourcePositiveGenerators SΓ
      change
        sourceAlphaInclusion
          (i :
            SoficGroups.prefixElementaryGroup
              SoficGroups.alphaPrefixCode) ∈
          SΓ.image sourceAlphaInclusion ∪
            {sourceCompressionU, sourceCompressionV}
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr
        ⟨(i :
          SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode), i.property, rfl⟩
    · fin_cases i
      · change sourceCompressionU ∈
          sourcePositiveGenerators SΓ
        change sourceCompressionU ∈
          SΓ.image sourceAlphaInclusion ∪
            {sourceCompressionU, sourceCompressionV}
        exact Finset.mem_union_right _ (by simp)
      · change sourceCompressionV ∈
          sourcePositiveGenerators SΓ
        change sourceCompressionV ∈
          SΓ.image sourceAlphaInclusion ∪
            {sourceCompressionU, sourceCompressionV}
        exact Finset.mem_union_right _ (by simp)
  · intro hx
    change
      x ∈ SΓ.image sourceAlphaInclusion ∪
        {sourceCompressionU, sourceCompressionV} at hx
    rcases Finset.mem_union.mp hx with hcorner | htables
    · obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp hcorner
      refine ⟨Sum.inl ⟨g, hg⟩, ?_⟩
      exact heq
    · simp only [Finset.mem_insert, Finset.mem_singleton] at htables
      rcases htables with rfl | rfl
      · refine ⟨Sum.inr (0 : Fin 2), ?_⟩
        rfl
      · refine ⟨Sum.inr (1 : Fin 2), ?_⟩
        rfl
end SoficGroups.KunExactActualSourceAmbientGenerators
