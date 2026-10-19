-- Prove2me | solution 1 for SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement_conjugates_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/f2ac7518-5f42-4402-aabd-c621316c768a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceBothCompressionNormalization
namespace SoficGroups.SourceBothCompressionNormalization
theorem _root_.solution
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    sourceCompressionUElement * sourceAlphaElement g *
        sourceCompressionUElement⁻¹ =
      sourceAlphaElement (sourceConjugatedAlphaUElement g) := by
  apply Subtype.ext
  rfl
end SoficGroups.SourceBothCompressionNormalization
