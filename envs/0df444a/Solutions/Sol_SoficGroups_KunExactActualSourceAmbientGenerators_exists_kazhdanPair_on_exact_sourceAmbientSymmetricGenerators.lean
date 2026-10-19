-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.exists_kazhdanPair_on_exact_sourceAmbientSymmetricGenerators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/70be6712-4b34-437b-9c03-b91d24c55a43

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunExactKazhdanGeneratorChange_exists_kazhdanPair_with_exact_symmetric_generators
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAmbientSymmetricGenerators_inv_mem
import Theorems.Thm_SoficGroups_KunExactActualSourceAmbientGenerators_sourceAmbientSymmetricGenerators_generate

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
            SoficGroups.alphaPrefixCode)) = ⊤)
    [SoficGroups.HasPropertyT.{0, 0}
      (SoficGroups.prefixElementaryGroup
        SoficGroups.ninePrefixCode)] :
    ∃ P : SoficGroups.KazhdanPair.{0, 0}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.ninePrefixCode),
      P.generators = sourceAmbientSymmetricGenerators SΓ := by
  exact exists_kazhdanPair_with_exact_symmetric_generators
    (sourceAmbientSymmetricGenerators SΓ)
    (sourceAmbientSymmetricGenerators_inv_mem SΓ)
    (sourceAmbientSymmetricGenerators_generate SΓ hgeneratesΓ)
end SoficGroups.KunExactActualSourceAmbientGenerators
