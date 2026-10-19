-- Prove2me | solution 1 for SoficGroups.SourceTopLevelCompressionFinal.ninePrefixElementaryGroup_not_sofic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/451e80a9-b50c-4ecc-9b1f-d19148fae60d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sourceLocalPrefixTranspositionGroup_notLEF
import Theorems.Thm_SoficGroups_SourceTopLevelCompressionFinal_sourceLocalPrefixTranspositionGroup_lef_of_sofic

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels
namespace SoficGroups.SourceTopLevelCompressionFinal
theorem _root_.solution :
    ¬ SoficGroups.Sofic
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) := by
  intro hsource
  exact SoficGroups.sourceLocalPrefixTranspositionGroup_notLEF
    (sourceLocalPrefixTranspositionGroup_lef_of_sofic hsource)
end SoficGroups.SourceTopLevelCompressionFinal
