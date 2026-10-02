-- Prove2me | solution 1 for ResourceScheduling.Graph.reduceWord_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T06:19:42.195377+00:00
-- url     : https://prove2.me/submissions/26f6cf3a-df0d-474b-83b1-59c41f46d49c

import Definitions.Def_ResourceScheduling_Graph_WordReduction
import Theorems.Thm_ResourceScheduling_Graph_encQ2_injective
import Theorems.Thm_ResourceScheduling_Graph_graph_decoder_correct
import Theorems.Thm_ResourceScheduling_Graph_paths_iff_q2Schedule
import Theorems.Thm_ResourceScheduling_Graph_q2_construct_encoding_length_le

set_option autoImplicit false

open ResourceScheduling.Graph

private theorem reduced_yes (d : GraphData) :
    Q2Yes (![2, 1], reduce d) ↔ PartitionIntoPathsOfLength2 d.G := by
  have hq : (fun i : Fin 2 => (((![2, 1] : Fin 2 → ℕ+) i : ℕ) : ℝ)) = ![2, 1] := by
    funext i
    fin_cases i <;> norm_num
  simpa only [Q2Yes, hq, reduce, construct] using (paths_iff_q2Schedule d).symm

private theorem empty_not_Q2 : [] ∉ codeLang Q2Yes encQ2 := by
  rintro ⟨p, _, he⟩
  have h := congrArg List.length he
  simp [encQ2, unary] at h

private theorem word_correct (w : List Letter) :
    w ∈ pathsLang ↔ reduceWord w ∈ codeLang Q2Yes encQ2 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    unfold reduceWord
    rw [graph_decoder_correct.1 d]
    exact ⟨(![2, 1], reduce d), (reduced_yes d).mpr hd, rfl⟩
  · intro h
    cases hd : decodeGraph w with
    | none =>
      have he : reduceWord w = [] := by simp [reduceWord, hd]
      rw [he] at h
      exact False.elim (empty_not_Q2 h)
    | some d =>
      rcases h with ⟨p, hp, he⟩
      have hcode : encQ2 (![2, 1], reduce d) = encQ2 p := by
        simpa only [reduceWord, hd] using he
      have hp' : p = (![2, 1], reduce d) := (encQ2_injective hcode).symm
      subst p
      exact ⟨d, (reduced_yes d).mp hp, (graph_decoder_correct.2 w d hd).symm⟩

/-- The total transformation preserves membership and has quadratic output size
on every word, including malformed inputs. -/
theorem solution (w : List Letter) :
    (w ∈ pathsLang ↔ reduceWord w ∈ codeLang Q2Yes encQ2) ∧
    (reduceWord w).length ≤ 5 * w.length ^ 2 + 8 := by
  refine ⟨word_correct w, ?_⟩
  cases hd : decodeGraph w with
  | none => simp [reduceWord, hd]
  | some d =>
    have he : reduceWord w = encQ2 (![2, 1], reduce d) := by simp [reduceWord, hd]
    rw [he, ← graph_decoder_correct.2 w d hd]
    exact q2_construct_encoding_length_le d

#print axioms solution
