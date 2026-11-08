-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rxOutput_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:52:36.568949+00:00
-- url     : https://prove2.me/submissions/1c297616-d0ae-41fd-a7c6-c86f3a07a43b

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_coarse_graining_odd


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
    {X Q Z : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
    {i : StepIndex depth}
    {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
    {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
    {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
    (A : RXCoarseGraining.RXCoarseGrainingData
      (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (hOdd : i.succ.val % 2 = 1)
    (sigma : D.family.Syndrome i.succ) :
    2 * HammingWeight ((rxOutput A hOdd sigma).coarse :
      D.family.Cochain2 i.castSucc) ≤
      HammingWeight (sigma : D.family.Cochain2 i.succ) := by
  let hsrc :=
    RXCoarseGraining.RXCoarseGrainingData.rx_coarse_graining_odd A hOdd sigma
  let hsrc' := Classical.choose_spec hsrc
  have hweight := (Classical.choose_spec hsrc').2.2.2.1
  exact hweight
end QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters
