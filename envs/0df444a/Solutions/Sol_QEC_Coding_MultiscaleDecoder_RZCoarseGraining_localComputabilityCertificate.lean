-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localComputabilityCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:10:17.13014+00:00
-- url     : https://prove2.me/submissions/6eabb9ae-4f34-4a31-877e-7d5c084bfcda

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_supported
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_correction_masked_eq_component
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_eq_xi_one
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_topParity_eq_xi_two

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData
namespace QEC.Coding.MultiscaleDecoder.RZCoarseGraining
theorem _root_.solution
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A) :
    RZLocalComputabilityCertificate A hcoh hcompat := by
  refine
    { totalCorrectionDecomposition := ?_
      componentSupported := ?_
      maskedTotalCorrectionEqComponent := ?_
      componentInvariantAtXiOne := ?_
      coarseCoordinateInvariantAtXiTwo := ?_ }
  · intro sigma
    rfl
  · intro z sigma q hq
    exact localCorrectionComponent_supported A hcoh z sigma q hq
  · intro z sigma
    exact correction_masked_eq_component A hcoh z sigma
  · intro sigma z
    exact localCorrectionComponent_eq_xi_one A hcoh sigma z
  · intro sigma z
    change topParity A sigma.1 z = topParity A (xiSignal A sigma.1 z 2) z
    exact topParity_eq_xi_two A sigma.1 z
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
