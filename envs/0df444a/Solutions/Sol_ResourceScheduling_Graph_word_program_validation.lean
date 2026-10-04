-- Prove2me | solution 1 for ResourceScheduling.Graph.word_program_validation
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:52.524884+00:00
-- url     : https://prove2.me/submissions/6442fc7f-ff8b-42ee-96d8-d9f6c5d57ada

import Definitions.Def_ResourceScheduling_Graph_WordProgram

set_option autoImplicit false
open ResourceScheduling.Graph

/-- The bounded natural-index Boolean check is exactly the original graph validity condition. -/
theorem solution (n : ℕ) (bits : List Letter) :
    checkGraphBody n bits = true ↔ ValidGraphBody n bits := by
  simp only [checkGraphBody, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, ValidGraphBody, rawAdj]
  constructor
  · rintro ⟨hlen, h⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro i j hij
      exact (h i.val i.isLt).2 j.val j.isLt hij
    · intro i
      exact (h i.val i.isLt).1
  · rintro ⟨hlen, hsymm, hdiag⟩
    refine ⟨hlen, fun i hi => ?_⟩
    exact ⟨hdiag ⟨i, hi⟩, fun j hj => hsymm ⟨i, hi⟩ ⟨j, hj⟩⟩

#print axioms solution
