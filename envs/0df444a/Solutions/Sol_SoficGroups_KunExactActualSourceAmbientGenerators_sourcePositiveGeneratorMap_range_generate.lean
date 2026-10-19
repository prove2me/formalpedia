-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap_range_generate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/a5ae0326-2204-485d-aa5a-8ef827ca4363

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_range_sourcePositiveGeneratorMap
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourcePositiveGenerators_generate

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
      (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ := by
  rw [range_sourcePositiveGeneratorMap]
  exact sourcePositiveGenerators_generate SΓ hgeneratesΓ
end SoficGroups.KunExactActualSourceAmbientGenerators
