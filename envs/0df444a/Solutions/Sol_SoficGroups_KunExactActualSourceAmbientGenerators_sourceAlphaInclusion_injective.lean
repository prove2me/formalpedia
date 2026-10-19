-- Prove2me | solution 1 for SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/aa1bf7e4-d8db-4056-aeac-d6d3136c052b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunExactKazhdanGeneratorChange
namespace SoficGroups.KunExactActualSourceAmbientGenerators
theorem _root_.solution :
    Function.Injective sourceAlphaInclusion := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z :
      SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode =>
        z.val) hxy
end SoficGroups.KunExactActualSourceAmbientGenerators
