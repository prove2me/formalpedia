-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.card_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:09:25.212214+00:00
-- url     : https://prove2.me/submissions/4540c3b5-2ab4-4610-b34d-da496e36f3fd

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (D : IntervalFamily n) (J : Finset (Fin (n + 1))) :
    (D.glue J).D.card = D.D.card + J.card := by
  have h : (D.glue J).D = D.D.image (Prod.map Fin.castSucc Fin.castSucc) ∪
      J.image (fun a => (a, Fin.last n)) := by
    ext p
    rw [mem_glue, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨a, d, rfl, had⟩ | ⟨h2, h1⟩)
      · exact Or.inl ⟨(a, d), had, rfl⟩
      · exact Or.inr ⟨p.1, h1, Prod.ext rfl h2.symm⟩
    · rintro (⟨⟨a, d⟩, had, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact Or.inl ⟨a, d, rfl, had⟩
      · exact Or.inr ⟨rfl, ha⟩
  rw [h, Finset.card_union_of_disjoint, Finset.card_image_of_injective _
    (Fin.castSucc_injective n |>.prodMap (Fin.castSucc_injective n)),
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1)]
  rw [Finset.disjoint_left]
  rintro p hp hp'
  rw [Finset.mem_image] at hp hp'
  obtain ⟨⟨a, d⟩, -, rfl⟩ := hp
  obtain ⟨a', -, h⟩ := hp'
  rw [Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last d).ne h.2.symm
end PretorsionImageClosed.LinearQuiver
