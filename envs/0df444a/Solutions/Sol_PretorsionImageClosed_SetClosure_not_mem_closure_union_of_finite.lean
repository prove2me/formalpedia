-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.not_mem_closure_union_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:12:19.360435+00:00
-- url     : https://prove2.me/submissions/fa0a7ab8-8f9d-4280-8764-c1be5b1ca940

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hae : c.IsAntiExchange) {K Y : Set E} {b : E}
    (hK : c.IsClosed K) (hbK : b ∉ K) (hYfin : Y.Finite)
    (hY : Y ⊆ c (insert b K)) (hbY : b ∉ Y) :
    b ∉ c (K ∪ Y) := by
  induction Y, hYfin using Set.Finite.induction_on generalizing K with
  | empty =>
      simpa [hK.closure_eq] using hbK
  | @insert y Y hyY hYfin ih =>
      have hyb : y ≠ b := by
        intro hyb
        exact hbY (hyb ▸ mem_insert y Y)
      have hbY' : b ∉ Y := fun hb ↦ hbY (mem_insert_of_mem y hb)
      by_cases hyK : y ∈ K
      · have hnot := ih hK hbK
          (fun z hz ↦ hY (mem_insert_of_mem y hz)) hbY'
        rw [show K ∪ insert y Y = K ∪ Y by
          ext z
          simp only [mem_union, mem_insert_iff]
          constructor
          · rintro (hzK | rfl | hzY)
            · exact Or.inl hzK
            · exact Or.inl hyK
            · exact Or.inr hzY
          · rintro (hzK | hzY)
            · exact Or.inl hzK
            · exact Or.inr (Or.inr hzY)]
        exact hnot
      · let K' : Set E := c (insert y K)
        have hK' : c.IsClosed K' := c.isClosed_closure _
        have hyAvailable : y ∈ c (insert b K) := hY (mem_insert y Y)
        have hbK' : b ∉ K' :=
          hae hK hyK hbK hyb hyAvailable
        have hKK' : K ⊆ K' := by
          intro z hz
          exact c.le_closure (insert y K) (mem_insert_of_mem y hz)
        have hY' : Y ⊆ c (insert b K') := by
          intro z hz
          apply c.monotone _ (hY (mem_insert_of_mem y hz))
          exact Set.insert_subset_insert hKK'
        have hnot := ih hK' hbK' hY' hbY'
        intro hb
        apply hnot
        have heq : c (K' ∪ Y) = c (K ∪ insert y Y) := by
          dsimp [K']
          calc
            c (c (insert y K) ∪ Y) = c (insert y K ∪ Y) := by
              change c (c (insert y K) ⊔ Y) = c (insert y K ⊔ Y)
              exact c.closure_sup_closure_left _ _
            _ = c (K ∪ insert y Y) := by
              congr 1
              ext z
              simp [or_left_comm, or_comm]
        exact heq.symm ▸ hb
end PretorsionImageClosed.SetClosure
