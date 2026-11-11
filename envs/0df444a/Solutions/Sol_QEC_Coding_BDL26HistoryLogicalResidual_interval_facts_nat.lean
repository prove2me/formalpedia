-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.interval_facts_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:29:50.911458+00:00
-- url     : https://prove2.me/submissions/7736fe6b-825c-46a8-a7f8-15c9a82e1f0f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_cocycleEdge_word
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_self
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_succ
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_self
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_succ
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap1_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap1_succ
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (w : FC.Cocycle S (a.val+2)) :
    (intervalCocycle S n a ⟨b,Nat.lt_succ_of_le hb⟩ ha w).val =
        intervalMap1 (SuffixData S n) a ⟨b,Nat.lt_succ_of_le hb⟩ ha w.val ∧
      suffixEquiv S n a ⟨b,Nat.lt_succ_of_le hb⟩ (FC.classOf S (a.val+2) w) =
        FC.classOf S (b+2) (intervalCocycle S n a ⟨b,Nat.lt_succ_of_le hb⟩ ha w) := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      constructor
      · rw [intervalCocycle_self,intervalMap1_self]; rfl
      · rw [suffixEquiv_self,intervalCocycle_self]; rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        constructor
        · rw [intervalCocycle_self,intervalMap1_self]; rfl
        · rw [suffixEquiv_self,intervalCocycle_self]; rfl
      · have hal : a.val ≤ b := by omega
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        have hf := ih (by omega) a hal w
        have hv := hf.1
        have hq := hf.2
        change (intervalCocycle S n a i.castSucc hal w).val =
          intervalMap1 (SuffixData S n) a i.castSucc hal w.val at hv
        change suffixEquiv S n a i.castSucc (FC.classOf S (a.val+2) w) =
          FC.classOf S (i.castSucc.val+2) (intervalCocycle S n a i.castSucc hal w) at hq
        change (intervalCocycle S n a i.succ ha w).val =
            intervalMap1 (SuffixData S n) a i.succ ha w.val ∧
          suffixEquiv S n a i.succ (FC.classOf S (a.val+2) w) =
            FC.classOf S (i.succ.val+2) (intervalCocycle S n a i.succ ha w)
        rw [intervalCocycle_succ S n a i hal,LinearMap.comp_apply]
        constructor
        · rw [cocycleEdge_word,hv,intervalMap1_succ _ a i hal,LinearMap.comp_apply]
        · rw [suffixEquiv_succ,hq]
          exact FC.stepEquiv_mk S (i.val+2) (intervalCocycle S n a i.castSucc hal w)
end QEC.Coding.BDL26HistoryLogicalResidual
