-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGenerators_generate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/b9aeac7d-42a1-4f24-ab15-ee5a55073f9b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAmbientSymmetricGenerators_generate

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
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
      (sourcePositiveGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) = ⊤ := by
  classical
  let K : Subgroup
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :=
    Subgroup.closure
      (sourcePositiveGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode))
  have hcontain :
      (sourceAmbientSymmetricGenerators SΓ : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) ⊆
        (K : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode)) := by
    intro x hx
    have hcases :
        x = 1 ∨
          x ∈ sourcePositiveGenerators SΓ ∨
          x⁻¹ ∈ sourcePositiveGenerators SΓ := by
      simpa [sourceAmbientSymmetricGenerators,
        Finset.mem_image] using hx
    rcases hcases with rfl | hxpositive | hxinverse
    · exact K.one_mem
    · exact Subgroup.subset_closure hxpositive
    · simpa using
        K.inv_mem (Subgroup.subset_closure hxinverse)
  have hle :
      Subgroup.closure
        (sourceAmbientSymmetricGenerators SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode)) ≤ K := by
    rw [Subgroup.closure_le]
    exact hcontain
  have htop :
      (⊤ : Subgroup
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)) ≤ K := by
    rw [← sourceAmbientSymmetricGenerators_generate SΓ hgeneratesΓ]
    exact hle
  exact top_unique htop
end SoficGroups.KunExactActualSourceAmbientGenerators
