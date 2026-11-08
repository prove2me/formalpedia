-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal_eq_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:00:40.620094+00:00
-- url     : https://prove2.me/submissions/ab2e1fc8-61f9-47cb-af88-4937a6a1624c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
theorem _root_.solution
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) :
    cqComponentTotal A sigma q =
      extendWordLinear (Lq.correctionRegion q)
        (cqWitnessAt A sigma q h) := by
  classical
  rw [cqComponentTotal, dif_pos h]
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
