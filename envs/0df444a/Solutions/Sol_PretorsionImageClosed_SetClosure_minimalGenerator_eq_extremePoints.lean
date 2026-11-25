-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.minimalGenerator_eq_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:43:01.459832+00:00
-- url     : https://prove2.me/submissions/3706f721-db4a-4f28-8646-b92ad6be177e

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Theorems.Thm_PretorsionImageClosed_SetClosure_not_mem_closure_union_of_finite
public import Theorems.Thm_PretorsionImageClosed_SetClosure_extremePoints_subset_of_closure_eq
public import Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution [Finite E]
    (hae : c.IsAntiExchange) {B C : Set E}
    (hC : c.IsClosed C) (hB : c.IsMinimalGenerator B C) :
    B = c.extremePoints C := by
  apply Set.Subset.antisymm
  · intro b hbB
    rw [mem_extremePoints]
    have hbC : b ∈ C := hB.1 ▸ c.le_closure B hbB
    refine ⟨hbC, ?_⟩
    have hbK : b ∉ c (B \ {b}) := by
      intro hb
      apply hB.2 hbB
      apply Set.Subset.antisymm
      · exact c.closure_min
          (fun z hz ↦ hB.1 ▸ c.le_closure B (sdiff_subset hz)) hC
      · intro z hzC
        have hzClosureB : z ∈ c B := hB.1.symm ▸ hzC
        have hBsub : B ⊆ c (B \ {b}) := by
          intro w hwB
          by_cases hwb : w = b
          · subst w
            exact hb
          · exact c.le_closure (B \ {b}) ⟨hwB, by simpa using hwb⟩
        have hz := c.monotone hBsub hzClosureB
        simpa using hz
    let K : Set E := c (B \ {b})
    have hK : c.IsClosed K := c.isClosed_closure _
    have hBinsert : B ⊆ insert b K := by
      intro z hzB
      by_cases hzb : z = b
      · simp [hzb]
      · exact mem_insert_of_mem b
          (c.le_closure (B \ {b}) ⟨hzB, by simpa using hzb⟩)
    have hCavailable : C ⊆ c (insert b K) := by
      intro z hzC
      exact c.monotone hBinsert (hB.1.symm ▸ hzC)
    have hYfin : (C \ {b}).Finite := Set.toFinite _
    have hnot : b ∉ c (K ∪ (C \ {b})) :=
      not_mem_closure_union_of_finite hae hK hbK hYfin
        (fun z hz ↦ hCavailable hz.1) (by simp)
    intro hb
    exact hnot (c.monotone (subset_union_right) hb)
  · exact extremePoints_subset_of_closure_eq hB.1
end PretorsionImageClosed.SetClosure
