-- Prove2me | solution 1 for SoficGroups.SourceTopLevelCompressionFinal.binaryLeavittElementaryGroup_not_sofic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/3e88760f-88fe-47de-aa57-2ab177d7ab1e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sofic_of_injective
import Theorems.Thm_SoficGroups_SourceTopLevelCompressionFinal_ninePrefixElementaryGroup_not_sofic

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels
namespace SoficGroups.SourceTopLevelCompressionFinal
theorem _root_.solution :
    ¬ SoficGroups.Sofic (SoficGroups.binaryLeavittElementaryGroup 9) := by
  intro hsofic
  letI : SoficGroups.Sofic
    (SoficGroups.binaryLeavittElementaryGroup 9) := hsofic
  exact ninePrefixElementaryGroup_not_sofic
    (SoficGroups.sofic_of_injective
      SoficGroups.ninePrefixElementaryGroupEquiv.symm.toMonoidHom
      SoficGroups.ninePrefixElementaryGroupEquiv.symm.injective)
end SoficGroups.SourceTopLevelCompressionFinal
