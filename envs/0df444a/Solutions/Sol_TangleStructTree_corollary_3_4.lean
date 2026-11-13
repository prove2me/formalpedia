-- Prove2me | solution 1 for TangleStructTree.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:20.537337+00:00
-- url     : https://prove2.me/submissions/c0e192d3-ee90-4fdc-8c2b-5ecbe4199292

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Theorems.Thm_TangleStructTree_closure_eq
import Theorems.Thm_TangleStructTree_lemma_3_3

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma child_rev_mem (T : SepTree E) {v : List E} {x : E} (hx : x :: v ∈ T.nodes) :
    rev x :: v ∈ T.nodes := by
  obtain ⟨s, hs, -⟩ := T.split v (T.parent_mem x v hx) ⟨x, hx⟩
  rw [hs]
  rcases (hs x).mp hx with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (rev_rev _)

lemma child_not_mem (T : SepTree E) {v : List E} {x : E} (hx : x :: v ∈ T.nodes) :
    x ∉ labels v ∧ rev x ∉ labels v := by
  obtain ⟨s, hs, hsy⟩ := T.split v (T.parent_mem x v hx) ⟨x, hx⟩
  have hxs := (hs x).mp hx
  constructor
  · intro h
    rcases hxs with h1 | h1
    · exact (hsy x h).1 h1
    · exact (hsy x h).2 h1.symm.symm
  · intro h
    rcases hxs with h1 | h1
    · exact (hsy _ h).2 (by rw [h1])
    · exact (hsy _ h).1 (by rw [h1, rev_rev])

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.C34

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma not_mem_closure (T : SepTree E) (hT : T.Consistent) {v : List E} {x : E}
    (hx : x :: v ∈ T.nodes) : x ∉ sepClosure (labels v) := by
  have hv := T.parent_mem x v hx
  intro h
  rcases h with h | hreq
  · exact (child_not_mem T hx).1 h
  · obtain ⟨r, hr, -, hlt⟩ := ((TangleStructTree.closure_eq (labels v) (hT v hv)).1 x
      (child_not_mem T hx).1).mp hreq
    exact TangleStructTree.lemma_3_3 T hT v x hx r hr hlt

end TangleStructTree.Dev.C34

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.C34

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_corollary_3_4 (T : SepTree E) (hT : T.Consistent) (v : List E) (x : E)
    (hx : x :: v ∈ T.nodes) :
    ({x, rev x} : Set E) ∩ sepClosure (labels v) = ∅ ∧ ¬ Orients (sepClosure (labels v)) x := by
  have h1 := not_mem_closure T hT hx
  have h2 : rev x ∉ sepClosure (labels v) := by
    exact not_mem_closure T hT (child_rev_mem T hx)
  refine ⟨?_, fun h => h.elim h1 h2⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro (rfl | rfl)
  · exact h1
  · exact h2

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_corollary_3_4 := @TangleStructTree.chk_corollary_3_4
