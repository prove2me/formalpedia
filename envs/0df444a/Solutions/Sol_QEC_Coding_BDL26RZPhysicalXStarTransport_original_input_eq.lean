-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.original_input_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:26:14.067114+00:00
-- url     : https://prove2.me/submissions/e2cf78c4-8a1b-4056-8696-f86794d64286

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_eq
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixHistory_top_eq
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_self
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_succ
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
section HistoryBridge
open BDL26HistorySyndromeSensitivity
private theorem prefix_entry {d : Nat} {C0 C1 C2 : LevelIndex d → Type}
    [∀ k, Fintype (C0 k)] [∀ k, Fintype (C1 k)] [∀ k, Fintype (C2 k)]
    (D : BDL26DecoderData d C0 C1 C2) (st : AlternatingStepData D) (base : AuditedBaseDecoder D)
    (n : Nat) (hn : n ≤ d) (s : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex d) (ha : a.val ≤ n) :
    ∃ e ∈ prefixHistory D st base n hn s, e.inputSyndrome.1=a ∧
      HEq e.inputSyndrome.2 (prefixInput D st n hn s a ha) := by
  induction n generalizing a with
  | zero =>
    have hz : a=⟨0,Nat.lt_succ_of_le hn⟩ := Fin.ext (by change a.val=0; omega)
    subst a
    let b : RecursiveBaseLevelCorrection D :=
      {input := s,correction := base.decode s,relation := (base.rightInverse s).symm}
    refine ⟨.base b,?_,rfl,?_⟩
    · rw [prefixHistory]
      exact List.mem_singleton_self _
    · rw [prefixInput_self]
      rfl
  | succ n ih =>
    by_cases h : a.val=n+1
    · have ha' : a=⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext h
      subst a
      let k : StepIndex d := ⟨n,by omega⟩
      let out := st.step k s
      refine ⟨.step k out,?_,rfl,?_⟩
      · rw [prefixHistory]
        exact List.mem_cons_self
      · rw [prefixInput_self]
        exact heq_of_eq ((st.relation k).input_eq s)
    · have hal : a.val ≤ n := by omega
      obtain ⟨e,he,hae,his⟩ := ih (by omega) (st.step ⟨n,by omega⟩ s).coarse a hal
      refine ⟨e,?_,hae,?_⟩
      · rw [prefixHistory]
        exact List.mem_cons_of_mem _ he
      · rw [prefixInput_succ D st n hn s a hal]
        exact his
end HistoryBridge
section Adjacent
end Adjacent
end QEC.Coding.BDL26RZPhysicalXStarTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
open BDL26HistorySyndromeSensitivity
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution (S : OddScale) (n : Nat) (s : TopInput S n) (a : LevelIndex n) :
    BDL26CanonicalHistoryMarks.inputAt S n s a=actualInputs S n s a := by
  obtain ⟨e,he,ha,hi⟩ := prefix_entry (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n))
    (BDL26OwnerIncidenceMasks.actualBase S n) n (Nat.le_refl _) s a (Nat.le_of_lt_succ a.isLt)
  have hm : e ∈ BDL26OwnerIncidenceMasks.actualHistory S n s := by
    change e ∈ buildCorrectionHistory (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n))
      (BDL26OwnerIncidenceMasks.actualBase S n) s
    rw [← prefixHistory_top_eq (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n))
      (BDL26OwnerIncidenceMasks.actualBase S n) s]
    exact he
  have hh : HEq (BDL26CanonicalHistoryMarks.entryAt S n s a).inputSyndrome.2
      (actualInputs S n s a) := by
    rw [BDL26CanonicalHistoryMarks.entryAt_eq S n s a e hm ha]
    exact hi
  exact eq_of_heq (rec_heq_of_heq (BDL26CanonicalHistoryMarks.entryAt_spec S n s a).2 hh)
end QEC.Coding.BDL26RZPhysicalXStarTransport
