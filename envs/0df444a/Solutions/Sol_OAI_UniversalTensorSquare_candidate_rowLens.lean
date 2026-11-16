-- Prove2me | solution 1 for OAI.UniversalTensorSquare.candidate_rowLens
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:40:06.168506+00:00
-- url     : https://prove2.me/submissions/3877b57f-6af4-419c-9f7d-2f05e194c27a

import Mathlib
import Definitions.Def_OAIQ259US007

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CandidateColumns
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma candidate_rowLens_oai {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1 := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]
    simp [candidateLengths]
  apply List.ext_getElem
  · simp only [YoungDiagram.length_rowLens,hh,List.length_append,List.length_cons,
      List.length_nil,List.length_reverse,List.length_range',List.length_replicate]
    omega
  · intro i hi hj
    rw [YoungDiagram.get_rowLens,candidate_rowLen _ _ _ _ hM]
    by_cases hi0 : i = 0
    · subst i
      simp [candidateLengths]
    by_cases hi1 : i = 1
    · subst i
      simp [candidateLengths]
    have hi2 : 2 ≤ i := by omega
    have hlen : i < M+b+δ := by simpa only [YoungDiagram.length_rowLens,hh] using hi
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons,List.length_nil, Nat.zero_add]
    simp only [candidateLengths,ite_eq_right hi0,ite_eq_right hi1]
    by_cases him : i < M-2
    · rw [ite_eq_left him,List.getElem_append_left (by simp; omega),List.getElem_reverse,
        List.getElem_range']
      simp only [List.length_range',Nat.one_mul]
      omega
    · rw [ite_eq_right him,List.getElem_append_right (by simp; omega)]
      simp only [List.length_reverse,List.length_range']
      by_cases hib : i < M-1+b
      · rw [ite_eq_left hib,List.getElem_append_left (by simp; omega),List.getElem_replicate]
      · rw [ite_eq_right hib,ite_eq_left hlen,List.getElem_append_right (by simp; omega),
          List.getElem_replicate]

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.candidate_rowLens_oai := @OAI.UniversalTensorSquare.candidate_rowLens_oai
