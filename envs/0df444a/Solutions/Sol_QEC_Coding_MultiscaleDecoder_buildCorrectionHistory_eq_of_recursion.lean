-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_eq_of_recursion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:53:11.161706+00:00
-- url     : https://prove2.me/submissions/15024d4e-e73f-4075-b5a2-e25993362555

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
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
namespace QEC.Coding.MultiscaleDecoder
theorem _root_.solution
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (F : ∀ (n : Nat) (hn : n ≤ depth),
      D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩ → CorrectionHistory D)
    (hzero : ∀ hn sigma, F 0 hn sigma = [.base {
      input := sigma, correction := B.decode sigma,
      relation := (B.rightInverse sigma).symm }])
    (hsucc : ∀ (n : Nat) (hn : n+1 ≤ depth)
      (sigma : D.family.Syndrome ⟨n+1,Nat.lt_succ_of_le hn⟩),
      F (n+1) hn sigma =
        .step ⟨n,by omega⟩ (S.step ⟨n,by omega⟩ sigma) ::
          F n (by omega) (S.step ⟨n,by omega⟩ sigma).coarse)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    buildCorrectionHistory D S B sigma = F depth (Nat.le_refl _) sigma := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩),
      buildHistoryAux D S B n hn s = F n hn s := by
    intro n
    induction n with
    | zero =>
        intro hn s
        rw [buildHistoryAux]
        change [CorrectionHistoryEntry.base ({
          input := s
          correction := B.decode s
          relation := (B.rightInverse s).symm
        } : RecursiveBaseLevelCorrection D)] = F 0 hn s
        exact (hzero hn s).symm
    | succ n ih =>
        intro hn s
        rw [buildHistoryAux]
        change CorrectionHistoryEntry.step (⟨n,by omega⟩ : StepIndex depth)
          (S.step ⟨n,by omega⟩ s) ::
            buildHistoryAux D S B n (by omega) (S.step ⟨n,by omega⟩ s).coarse = F (n+1) hn s
        rw [hsucc]
        exact congrArg (fun H => CorrectionHistoryEntry.step
          (⟨n,by omega⟩ : StepIndex depth) (S.step ⟨n,by omega⟩ s) :: H) (ih _ _)
  exact aux depth (Nat.le_refl _) sigma
end QEC.Coding.MultiscaleDecoder
