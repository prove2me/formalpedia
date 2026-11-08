-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rzOutput_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:28:31.689976+00:00
-- url     : https://prove2.me/submissions/554f38ac-24de-4005-9aad-09e8cf90f2e6

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_AuditedLeafAdapters_rzOutput_correction
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_exact_relation
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_selectedMap_map2_injective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
open QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters
open RZCoarseGraining RXCoarseGraining
variable {D : BDL26DecoderData depth C0 C1 C2}
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters
theorem _root_.solution
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).coarse =
      RZCoarseGraining.coarseSyndrome A hcompat sigma := by
  apply Subtype.ext
  apply RZCoarseGraining.selectedMap_map2_injective A hEven
  have hactual := (rzOutput A hcoh hcompat hEven sigma).relation
  change (sigma : D.family.Cochain2 i.succ) = _ at hactual
  rw [rzOutput_correction] at hactual
  have hcanonical := RZCoarseGraining.rz_exact_relation A hcoh hcompat hEven sigma
  exact add_left_cancel (hactual.symm.trans hcanonical)
end QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters
