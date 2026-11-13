-- Prove2me | solution 1 for TangleStructTree.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:18.982373+00:00
-- url     : https://prove2.me/submissions/2dbe786f-85a6-4df8-b50a-df3c2e0c8016

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma labels_cons (x : E) (v : List E) : labels (x :: v) = insert x (labels v) := by
  ext y; simp [labels]

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_3_3 (T : SepTree E) (hT : T.Consistent) (v : List E) (x : E)
    (hx : x :: v ∈ T.nodes) :
    ∀ y ∈ labels v, ¬ y < x := by
  intro y hy hlt
  have hv := T.parent_mem x v hx
  obtain ⟨s, hs, hsy⟩ := T.split v hv ⟨x, hx⟩
  have hxs := (hs x).mp hx
  have hrx : rev x :: v ∈ T.nodes := by
    rw [hs]; rcases hxs with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (rev_rev _)
  -- y ∈ labels v, y ≠ x, y ≠ rev x
  have hyx : y ≠ rev x := by
    intro h
    rcases hxs with rfl | rfl
    · exact (hsy y hy).2 (by rw [h])
    · exact (hsy y hy).1 (by rw [h, rev_rev])
  have hcons := hT (rev x :: v) hrx
  have hy2 : y ∈ labels (rev x :: v) := by rw [labels_cons]; exact Set.mem_insert_of_mem _ hy
  have hrx2 : rev x ∈ labels (rev x :: v) := by rw [labels_cons]; exact Set.mem_insert _ _
  refine hcons y hy2 (rev x) hrx2 (fun h => hyx h.symm) ?_ ?_
  · intro h
    exact hlt.ne (by have := congrArg rev h; simpa [rev_rev] using this.symm)
  · simpa [rev_rev] using hlt.le

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_3_3 := @TangleStructTree.chk_lemma_3_3
