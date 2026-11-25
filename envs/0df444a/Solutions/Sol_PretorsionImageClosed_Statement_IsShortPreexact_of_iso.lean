-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsShortPreexact.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:30.62296+00:00
-- url     : https://prove2.me/submissions/09976b0a-a4a8-435f-8276-fceac94a28cb

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_DirectSums

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Zs : Subcategory C}
namespace PretorsionImageClosed.Statement
namespace IsShortPreexact
theorem _root_.solution {T X X' F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsShortPreexact Zs.prop u v) (e : X ≅ X') :
    IsShortPreexact Zs.prop (u ≫ e.hom) (e.inv ≫ v) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact h.1.1
  · intro Y u' hu'
    rw [← Category.assoc] at hu'
    obtain ⟨w, hw, huniq⟩ := h.1.2 _ hu'
    refine ⟨w, ?_, ?_⟩
    · show w ≫ u ≫ e.hom = u'
      rw [← Category.assoc, hw, Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro w' hw'
      have hw'' : w' ≫ u ≫ e.hom = u' := hw'
      apply huniq
      show w' ≫ u = u' ≫ e.inv
      rw [← hw'', Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact h.2.1
  · intro Y v' hv'
    rw [Category.assoc] at hv'
    obtain ⟨w, hw, huniq⟩ := h.2.2 _ hv'
    refine ⟨w, ?_, ?_⟩
    · show (e.inv ≫ v) ≫ w = v'
      rw [Category.assoc, hw, e.inv_hom_id_assoc]
    · intro w' hw'
      have hw'' : (e.inv ≫ v) ≫ w' = v' := hw'
      apply huniq
      show v ≫ w' = e.hom ≫ v'
      rw [← hw'']
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
end IsShortPreexact
end PretorsionImageClosed.Statement
