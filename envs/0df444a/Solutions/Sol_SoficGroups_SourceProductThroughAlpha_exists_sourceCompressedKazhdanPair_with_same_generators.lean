-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.exists_sourceCompressedKazhdanPair_with_same_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/fe06bc65-8f98-4c3f-a148-30d3a3a09df6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_alphaZeroPrefixElementaryGroup_hasPropertyT_unconditional
import Theorems.Thm_SoficGroups_KunExactKazhdanGeneratorChange_exists_kazhdanPair_with_exact_symmetric_generators

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
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤) :
    ∃ P : SoficGroups.KazhdanPair.{0, v}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode),
      P.generators = sourceCompressedGeneratingFinset SΓ := by
  letI : SoficGroups.HasPropertyT.{0, v}
      (SoficGroups.prefixElementaryGroup
        SoficGroups.alphaZeroPrefixCode) :=
    SoficGroups.alphaZeroPrefixElementaryGroup_hasPropertyT_unconditional
  exact
    SoficGroups.KunExactKazhdanGeneratorChange.exists_kazhdanPair_with_exact_symmetric_generators
      (sourceCompressedGeneratingFinset SΓ)
      (sourceCompressedGeneratingFinset_inv_mem SΓ hsymmetric)
      (sourceCompressedGeneratingFinset_closure SΓ hgenerates)
end SoficGroups.SourceProductThroughAlpha
