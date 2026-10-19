-- Prove2me | solution 1 for SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable_conjugates_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/a3b23dde-dc28-40a5-9a2f-baae61e36565

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceBothCompressionNormalization_sourceCompressionUElement_conjugates_alpha
import Theorems.Thm_SoficGroups_SourceBothCompressionNormalization_sourceCompressionVElement_conjugates_alpha

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceBothCompressionNormalization
namespace SoficGroups.SourceBothCompressionNormalization
theorem _root_.solution
    (i : Fin 2)
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    ∃ k : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode,
      sourceCompressionTable i * sourceAlphaElement g *
          (sourceCompressionTable i)⁻¹ =
        sourceAlphaElement k := by
  fin_cases i
  · exact ⟨sourceConjugatedAlphaUElement g,
      sourceCompressionUElement_conjugates_alpha g⟩
  · exact ⟨sourceConjugatedAlphaVElement g,
      sourceCompressionVElement_conjugates_alpha g⟩
end SoficGroups.SourceBothCompressionNormalization
