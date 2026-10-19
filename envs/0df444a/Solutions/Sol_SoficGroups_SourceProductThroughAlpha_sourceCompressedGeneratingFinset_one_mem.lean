-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/5f240e6a-9467-431a-ba6b-4a39c5db13b4

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
theorem _root_.solution
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hone : 1 ∈ SΓ) :
    1 ∈ sourceCompressedGeneratingFinset SΓ := by
  classical
  change 1 ∈ SΓ.image sourceCompressionUAlphaEquiv
  exact Finset.mem_image.mpr
    ⟨1, hone, map_one sourceCompressionUAlphaEquiv⟩
end SoficGroups.SourceProductThroughAlpha
