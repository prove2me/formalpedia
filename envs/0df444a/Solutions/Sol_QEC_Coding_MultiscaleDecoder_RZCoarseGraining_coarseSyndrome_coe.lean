-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:25:38.417281+00:00
-- url     : https://prove2.me/submissions/487a6546-6e87-4974-80ca-b8d85f4439be

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining

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
    (sigma : UpperSyndrome D i) :
    (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) =
      topParity A sigma.1 :=
  rfl
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
