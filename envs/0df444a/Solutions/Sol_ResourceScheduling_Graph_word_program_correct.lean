-- Prove2me | solution 1 for ResourceScheduling.Graph.word_program_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:55.001332+00:00
-- url     : https://prove2.me/submissions/37e45f4f-992b-4a9d-9dc7-f1bae4fe2634

import Theorems.Thm_ResourceScheduling_Graph_word_program_validation
import Theorems.Thm_ResourceScheduling_Graph_word_program_emitter

set_option autoImplicit false
open ResourceScheduling.Graph

/-- The explicit bounded-list program is extensionally equal to the original reduction. -/
theorem solution : wordProgram = reduceWord := by
  funext w
  unfold wordProgram reduceWord decodeGraph
  cases hp : readUnary w with
  | none => rfl
  | some p =>
    rcases p with ⟨t, bits⟩
    by_cases hv : ValidGraphBody (3 * t) bits
    · have hc := (word_program_validation (3 * t) bits).2 hv
      simp only [hc, hv, ↓reduceIte, reduce]
      apply word_program_emitter
      intro i j
      rfl
    · have hc : checkGraphBody (3 * t) bits ≠ true := by
        intro h
        exact hv ((word_program_validation (3 * t) bits).1 h)
      simp [hc, hv]

#print axioms solution
