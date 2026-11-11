-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.prefixHistory_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:47:59.514361+00:00
-- url     : https://prove2.me/submissions/642e86fb-0b9c-426f-8451-f186632263a1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩) :
    ∀ e ∈ prefixHistory D S B n hn sigma, e.inputSyndrome.1.val ≤ n := by
  induction n with
  | zero =>
      intro e he
      rw [prefixHistory] at he
      have he' : e = .base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm } := List.mem_singleton.mp he
      subst e
      exact Nat.le_refl 0
  | succ n ih =>
      intro e he
      rw [prefixHistory] at he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact Nat.le_refl _
      · exact (ih _ _ e he).trans (Nat.le_succ n)
end QEC.Coding.BDL26HistorySyndromeSensitivity
