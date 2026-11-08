-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.cqCorrectionTotal_eq_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:48:57.490286+00:00
-- url     : https://prove2.me/submissions/4e667ca9-216c-47e8-85b3-31c5cad780ef

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_cqCorrectionTotal_eq_explicit
section
namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
namespace RXCoarseGrainingData
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
private theorem cqWitnessRG_spec
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q (cqWitnessRG A sigma hlocal q) =
        restrictWordLinear (Lq.syndromeRegion q) sigma ∧
      HammingWeight (A.contract.support_decomposition.cqFlow q
        (cqWitnessRG A sigma hlocal q)) ≤
        HammingWeight (restrictWordLinear (Lq.syndromeRegion q) sigma) := by
  intro q
  exact Classical.choose_spec (A.contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))
end RXCoarseGrainingData
end RXCoarseGraining
end MultiscaleDecoder
end Coding
end QEC
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
namespace RXCoarseGrainingData
end RXCoarseGrainingData
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining
end

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
    (sigma : D.family.Cochain2 i.succ)
    (h : CqLocalRange A sigma)
    (w : ∀ q, Word Field (LocalRegionIndex (Lq.correctionRegion q)))
    (huniq : ∀ q f,
      (A.contract.rx_local_complexes.cqDelta1 q f =
          restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A sigma) ∧
        HammingWeight (A.contract.support_decomposition.cqFlow q f) ≤
          HammingWeight (restrictWordLinear (Lq.syndromeRegion q)
            (rxSigmaAfterCx A sigma))) → f = w q) :
    cqCorrectionTotal A sigma =
      ∑ q : Q, extendWordLinear (Lq.correctionRegion q) (w q) := by
  rw [cqCorrectionTotal_eq_explicit A sigma h]
  unfold cqCorrectionRG
  apply Finset.sum_congr rfl
  intro q hq
  have hspec := (cqWitnessRG_spec A (rxSigmaAfterCx A sigma)
    (fun q => h q) q).1
  rw [huniq q (cqWitnessRG A (rxSigmaAfterCx A sigma) (fun q => h q) q)
    (cqWitnessRG_spec A (rxSigmaAfterCx A sigma) (fun q => h q) q)]
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
