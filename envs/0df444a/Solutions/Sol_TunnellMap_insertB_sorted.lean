-- Prove2me | solution 1 for TunnellMap.insertB_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:32.594209+00:00
-- url     : https://prove2.me/submissions/18263c71-fc7b-4b3f-bc74-e71efdd7749e

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_insertB_perm
attribute [local simp] TunnellMap.isqrtK_eq

set_option autoImplicit true
open TunnellMap
variable {α : Type*}
namespace TunnellMap
theorem _root_.solution (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (a : α) {l : List α} (hl : l.Pairwise fun x y => le x y = true) :
    (insertB le a l).Pairwise fun x y => le x y = true := by
  induction l with
  | nil => simp [insertB]
  | cons b l ih =>
      rw [List.pairwise_cons] at hl
      by_cases h : le a b
      · simp only [insertB, h, if_true]
        refine List.Pairwise.cons ?_ (List.pairwise_cons.mpr hl)
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact htrans _ _ _ h (hl.1 y hy)
      · have hba : le b a = true := (htotal a b).resolve_left (by simpa using h)
        simp only [insertB, h, Bool.false_eq_true, if_false]
        refine List.Pairwise.cons ?_ (ih hl.2)
        intro y hy
        rcases List.mem_cons.mp ((insertB_perm le a l).mem_iff.mp hy) with rfl | hy'
        · exact hba
        · exact hl.1 y hy'
end TunnellMap
