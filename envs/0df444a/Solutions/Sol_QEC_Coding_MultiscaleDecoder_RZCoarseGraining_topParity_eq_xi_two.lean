-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.topParity_eq_xi_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:04.341505+00:00
-- url     : https://prove2.me/submissions/142e899e-a842-43ba-b967-d49381b63e55

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_sigma_agrees_xi_radius_two
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
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    topParity A sigma z = topParity A (xiSignal A sigma z 2) z := by
  exact coarseParity_invariant_radius_two A z sigma
    (xiSignal A sigma z 2) (sigma_agrees_xi_radius_two A sigma z)
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
