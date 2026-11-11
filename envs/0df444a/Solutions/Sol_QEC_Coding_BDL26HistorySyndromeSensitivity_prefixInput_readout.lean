-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.prefixInput_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:59:35.189098+00:00
-- url     : https://prove2.me/submissions/4c6baaac-a5b3-4447-9e17-3722eb8f0cc6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_self
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixInput_succ
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_historyReadout_step_same
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_historyReadout_step_ne
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefixReadout_above
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
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : a.val ≤ n) :
    historyInputReadout D (prefixHistory D S B n hn sigma) a =
      (prefixInput D S n hn sigma a ha).val := by
  induction n generalizing a with
  | zero =>
      have he : a = 0 := Fin.ext (by change a.val = 0; omega)
      subst a
      let b : RecursiveBaseLevelCorrection D := {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }
      have hh : prefixHistory D S B 0 hn sigma = [.base b] := by
        rw [prefixHistory]
        rfl
      have hr := congrArg (fun H : CorrectionHistory D => historyInputReadout D H 0) hh
      exact hr.trans ((historyInputReadout_base D b).trans
        (congrArg Subtype.val (prefixInput_self D S 0 hn sigma)).symm)
  | succ n ih =>
      by_cases he : a.val = n+1
      · have hea : a = ⟨n+1,Nat.lt_succ_of_le hn⟩ := Fin.ext he
        subst a
        let i : StepIndex depth := ⟨n,by omega⟩
        let out := S.step i sigma
        let tail := prefixHistory D S B n (by omega) out.coarse
        have hh : prefixHistory D S B (n+1) hn sigma = .step i out :: tail := by
          rw [prefixHistory]
        have hr := (congrArg (fun H : CorrectionHistory D =>
          historyInputReadout D H i.succ) hh).trans (historyReadout_step_same D i out tail)
        have ht := prefixReadout_above D S B n (by omega)
          out.coarse i.succ (by change n < n+1; omega)
        exact hr.trans ((congrArg (fun w => out.input.val + w) ht).trans
          ((add_zero _).trans
            ((congrArg Subtype.val ((S.relation i).input_eq sigma)).trans
              (congrArg Subtype.val (prefixInput_self D S (n+1) hn sigma)).symm)))
      · have hal : a.val ≤ n := by omega
        rw [prefixInput_succ D S n hn sigma a hal, prefixHistory]
        have hne : (⟨n,by omega⟩ : StepIndex depth).succ ≠ a := by
          intro h
          exact he (congrArg Fin.val h).symm
        exact (historyReadout_step_ne D _ _ _ a hne).trans (ih _ _ a hal)
end QEC.Coding.BDL26HistorySyndromeSensitivity
