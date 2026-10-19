-- Prove2me | solution 1 for SoficGroups.SourceBothCompressionNormalization.sourceCompressionVElement_conjugates_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/cf48ec8e-cbb8-42b9-bb54-e5a429345a40

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceBothCompressionNormalization
namespace SoficGroups.SourceBothCompressionNormalization
theorem _root_.solution
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    sourceCompressionVElement * sourceAlphaElement g *
        sourceCompressionVElement⁻¹ =
      sourceAlphaElement (sourceConjugatedAlphaVElement g) := by
  apply Subtype.ext
  rfl
end SoficGroups.SourceBothCompressionNormalization
