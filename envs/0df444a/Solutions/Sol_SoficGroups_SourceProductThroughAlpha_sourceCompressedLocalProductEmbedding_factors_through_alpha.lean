-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductEmbedding_factors_through_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/7002990c-926e-4732-a06d-7b1b278a521e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
universe v
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution :
    SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion.comp
        sourceCompressedLocalProductToAlpha =
      SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rfl
end SoficGroups.SourceProductThroughAlpha
