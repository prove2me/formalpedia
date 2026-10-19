-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.one_mem_sourceAmbientSymmetricGenerators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/c7356eed-a6d7-4217-aa52-7c515973e8e6

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunExactKazhdanGeneratorChange
namespace SoficGroups.KunExactActualSourceAmbientGenerators
theorem _root_.solution
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    1 ∈ sourceAmbientSymmetricGenerators SΓ := by
  classical
  simp [sourceAmbientSymmetricGenerators]
end SoficGroups.KunExactActualSourceAmbientGenerators
