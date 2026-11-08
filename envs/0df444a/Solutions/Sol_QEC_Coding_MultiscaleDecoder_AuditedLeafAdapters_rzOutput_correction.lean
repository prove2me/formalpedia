-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rzOutput_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:25:58.619441+00:00
-- url     : https://prove2.me/submissions/1b7bd98a-5cbc-4a06-9c3f-f3691a97b32b

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_coarse_graining_even


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
    (rzOutput A hcoh hcompat hEven sigma).correction =
      RZCoarseGraining.correctionFromSyndrome A hcoh sigma.1 := by
  let hsrc := RZCoarseGraining.rz_coarse_graining_even A hcoh hcompat hEven sigma
  exact (Classical.choose_spec (Classical.choose_spec hsrc)).1
end QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters
