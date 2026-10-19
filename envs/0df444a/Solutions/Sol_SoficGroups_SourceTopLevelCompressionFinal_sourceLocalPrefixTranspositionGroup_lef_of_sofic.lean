-- Prove2me | solution 1 for SoficGroups.SourceTopLevelCompressionFinal.sourceLocalPrefixTranspositionGroup_lef_of_sofic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/834fe770-47ea-4006-a6a0-e4f7d9cacc3a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceTopLevelCompression_sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
import Theorems.Thm_SoficGroups_KunLiteralNineSourceFiniteModels_source_ambient_nonempty_expandingCentralizerFiniteModel

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels
namespace SoficGroups.SourceTopLevelCompressionFinal
theorem _root_.solution :
    SoficGroups.Sofic
        (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) →
      SoficGroups.LEF
        (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
          SoficGroups.ThompsonPrefixLocal.sourceLocalWord) := by
  intro hsource
  exact sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
    (fun A _ F =>
      source_ambient_nonempty_expandingCentralizerFiniteModel A F)
    hsource
end SoficGroups.SourceTopLevelCompressionFinal
