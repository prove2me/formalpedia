-- Prove2me | solution 1 for SoficGroups.KunUnconditionalActualSourceGeneratorData.exists_unconditional_actual_source_generator_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/3d8da269-ed5c-438b-a825-a8387067a997

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_alphaPrefixElementaryGroup_hasPropertyT_unconditional
import Theorems.Thm_SoficGroups_ninePrefixElementaryGroup_hasPropertyT_unconditional
import Theorems.Thm_SoficGroups_KunExactKazhdanGeneratorChange_exists_kazhdanPair_with_exact_symmetric_generators
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAlphaInclusion_injective
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_one_mem_sourceAmbientSymmetricGenerators
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAmbientSymmetricGenerators_inv_mem
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAmbientSymmetricGenerators_generate
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourcePositiveGeneratorMap_range_generate
import Theorems.Thm_SoficGroups_KunUnconditionalActualSourceGeneratorData_exists_actual_source_alpha_symmetric_generators

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUnconditionalActualSourceGeneratorData
open SoficGroups.KunExactKazhdanGeneratorChange
open SoficGroups.KunExactActualSourceAmbientGenerators
namespace SoficGroups.KunUnconditionalActualSourceGeneratorData
theorem _root_.solution :
    ∃ (SΓ : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
      (PΓ : SoficGroups.KazhdanPair.{0, 0}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode))
      (PG : SoficGroups.KazhdanPair.{0, 0}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode)),
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤ ∧
      PΓ.generators = SΓ ∧
      1 ∈ sourceAmbientSymmetricGenerators SΓ ∧
      (∀ g ∈ sourceAmbientSymmetricGenerators SΓ,
        g⁻¹ ∈ sourceAmbientSymmetricGenerators SΓ) ∧
      Subgroup.closure
        (sourceAmbientSymmetricGenerators SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode)) = ⊤ ∧
      PG.generators = sourceAmbientSymmetricGenerators SΓ ∧
      Function.Injective sourceAlphaInclusion ∧
      Subgroup.closure
        (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ := by
  letI : SoficGroups.HasPropertyT.{0, 0}
      (SoficGroups.prefixElementaryGroup
        SoficGroups.alphaPrefixCode) :=
    SoficGroups.alphaPrefixElementaryGroup_hasPropertyT_unconditional
  letI : SoficGroups.HasPropertyT.{0, 0}
      (SoficGroups.prefixElementaryGroup
        SoficGroups.ninePrefixCode) :=
    SoficGroups.ninePrefixElementaryGroup_hasPropertyT_unconditional
  obtain ⟨SΓ, honeΓ, hsymmetricΓ, hgeneratesΓ⟩ :=
    exists_actual_source_alpha_symmetric_generators
  obtain ⟨PΓ, hPΓ⟩ :=
    exists_kazhdanPair_with_exact_symmetric_generators
      SΓ hsymmetricΓ hgeneratesΓ
  obtain ⟨PG, hPG⟩ :=
    exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
      SΓ hgeneratesΓ
  refine ⟨SΓ, PΓ, PG, honeΓ, hsymmetricΓ, hgeneratesΓ,
    hPΓ, one_mem_sourceAmbientSymmetricGenerators SΓ,
    sourceAmbientSymmetricGenerators_inv_mem SΓ,
    sourceAmbientSymmetricGenerators_generate SΓ hgeneratesΓ,
    hPG, sourceAlphaInclusion_injective, ?_⟩
  exact sourcePositiveGeneratorMap_range_generate SΓ hgeneratesΓ
end SoficGroups.KunUnconditionalActualSourceGeneratorData
