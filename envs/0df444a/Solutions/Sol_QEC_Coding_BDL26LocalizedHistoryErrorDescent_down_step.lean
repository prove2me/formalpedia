-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:12:47.078528+00:00
-- url     : https://prove2.me/submissions/caa22ec8-5d1d-4913-98e9-b4d53e9ff5dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_down_self
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_down_succ

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩)
    (i : StepIndex n) (hi : i.val < b) :
    down S n sigma tau b hb u i.castSucc (by change i.val ≤ b; omega)=
      (step S n sigma tau i (down S n sigma tau b hb u i.succ (by change i.val+1 ≤ b; omega))).lower := by
  induction b generalizing i with
  | zero => omega
  | succ b ih =>
      by_cases he : i.val=b
      · have hb_lt : b < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb
        let j : StepIndex n := ⟨b,hb_lt⟩
        have hei : i=j := Fin.ext he
        subst i
        have hlow : b ≤ n := Nat.le_trans (Nat.le_succ b) hb
        have hu : down S n sigma tau (b+1) hb u j.succ
            (by change b+1 ≤ b+1; exact Nat.le_refl _)=u := by
          change down S n sigma tau (b+1) hb u
            ⟨b+1,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _)=u
          exact down_self S n sigma tau (b+1) hb u
        rw [hu]
        rw [down_succ S n sigma tau b hb u j.castSucc
          (by change b ≤ b; exact Nat.le_refl _)]
        change down S n sigma tau b hlow (step S n sigma tau j u).lower
          ⟨b,Nat.lt_succ_of_le hlow⟩ (Nat.le_refl _)=(step S n sigma tau j u).lower
        exact down_self S n sigma tau b hlow (step S n sigma tau j u).lower
      · have hil : i.val+1 ≤ b := by omega
        rw [down_succ S n sigma tau b hb u i.castSucc (by change i.val ≤ b; omega),
          down_succ S n sigma tau b hb u i.succ hil]
        exact ih (by omega) _ i (by omega)
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
