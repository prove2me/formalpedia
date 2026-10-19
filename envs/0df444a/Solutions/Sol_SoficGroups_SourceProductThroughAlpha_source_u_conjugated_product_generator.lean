-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.source_u_conjugated_product_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/05368c80-2d5f-462f-9084-e8bd360f0452

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution
    (g : SoficGroups.prefixElementaryGroup
      SoficGroups.alphaPrefixCode) :
    SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
        (sourceCompressionUAlphaEquiv g, 1) =
      SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
        SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion g *
          (SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹ := by
  apply Subtype.ext
  change
    (sourceCompressionUAlphaEquiv g : SoficGroups.BinaryLeavittˣ) * 1 =
      SoficGroups.compressionU *
        (g : SoficGroups.BinaryLeavittˣ) *
          SoficGroups.compressionU⁻¹
  rw [mul_one]
  change
    (MulAut.conj SoficGroups.compressionU)
        (g : SoficGroups.BinaryLeavittˣ) =
      SoficGroups.compressionU *
        (g : SoficGroups.BinaryLeavittˣ) *
          SoficGroups.compressionU⁻¹
  rw [MulAut.conj_apply]
end SoficGroups.SourceProductThroughAlpha
