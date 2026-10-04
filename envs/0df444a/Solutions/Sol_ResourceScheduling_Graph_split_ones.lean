-- Prove2me | solution 1 for ResourceScheduling.Graph.split_ones
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:51:11.587626+00:00
-- url     : https://prove2.me/submissions/b4d4eae3-1009-4c05-a4a3-8d852645b5b7

import Definitions.Def_ResourceScheduling_Graph_RAMParse

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution (w : List Letter) :
    w = List.replicate (splitOnes w).1 Letter.one ++ (splitOnes w).2 ∧
    (splitOnes w).2.head? ≠ some Letter.one ∧
    (splitOnes w).1 + (splitOnes w).2.length = w.length ∧
    readUnary w = if (splitOnes w).2 = [] then none
      else some ((splitOnes w).1, (splitOnes w).2.tail) := by
  induction w with
  | nil => simp [splitOnes, readUnary]
  | cons a w ih =>
    cases a with
    | sep => simp [splitOnes, readUnary]
    | one =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [splitOnes, List.replicate_succ] using congrArg (List.cons Letter.one) ih.1
      · exact ih.2.1
      · simp only [splitOnes, List.length_cons]; omega
      · simp only [readUnary, ih.2.2.2, splitOnes]
        by_cases h : (splitOnes w).2 = [] <;> simp [h]

#print axioms solution
