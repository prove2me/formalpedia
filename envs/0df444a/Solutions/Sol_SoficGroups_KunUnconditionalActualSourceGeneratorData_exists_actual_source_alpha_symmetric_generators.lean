-- Prove2me | solution 1 for SoficGroups.KunUnconditionalActualSourceGeneratorData.exists_actual_source_alpha_symmetric_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/a42f23e6-f4c8-4293-8abe-997c81e92ee4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_alphaPrefixElementaryGroup_finitelyGenerated
import Theorems.Thm_SoficGroups_KunUnconditionalActualSourceGeneratorData_exists_symmetric_generating_finset_of_finitelyGenerated

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUnconditionalActualSourceGeneratorData
open SoficGroups.KunExactKazhdanGeneratorChange
open SoficGroups.KunExactActualSourceAmbientGenerators
namespace SoficGroups.KunUnconditionalActualSourceGeneratorData
theorem _root_.solution :
    ∃ SΓ : Finset
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode),
      1 ∈ SΓ ∧
        (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
        Subgroup.closure
          (SΓ : Set
            (SoficGroups.prefixElementaryGroup
              SoficGroups.alphaPrefixCode)) = ⊤ :=
  exists_symmetric_generating_finset_of_finitelyGenerated
    SoficGroups.alphaPrefixElementaryGroup_finitelyGenerated
end SoficGroups.KunUnconditionalActualSourceGeneratorData
