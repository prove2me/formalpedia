-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_invariant_radius_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:30:40.029382+00:00
-- url     : https://prove2.me/submissions/93c75c52-776e-4251-9b21-bbdaf71f362f

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseParity_invariant_radius_two

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
    (hcompat : InducedCoboundaryCompatibility A)
    (z : C2 i.castSucc)
    (sigma tau : UpperSyndrome D i)
    (hAgree : SignalAgreementWithin A z 2 sigma.1 tau.1) :
    (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
      (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z := by
  exact coarseParity_invariant_radius_two A z sigma.1 tau.1 hAgree
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
