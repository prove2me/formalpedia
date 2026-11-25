-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPretorsionTheory.isSubobjectClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:07:51.434987+00:00
-- url     : https://prove2.me/submissions/7824bb0e-2b08-4cff-a8d5-6475504704e4

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_epi

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}
variable [HasZeroMorphisms C] [HasBinaryBiproducts C] [Balanced C]
namespace PretorsionImageClosed.Statement
namespace IsPretorsionTheory
theorem _root_.solution {T F : Subcategory C}
    (h : IsPretorsionTheory T.prop F.prop) : F.IsSubobjectClosed := by
  intro X Y i hi hY
  obtain ⟨T', F', u, v, hT', hF', hu, hv⟩ := h.2 X
  -- `u ≫ i` is trivial, so `i` factors through the precokernel `v`
  obtain ⟨w, hw, -⟩ := hv.2 i (h.1 (u ≫ i) hT' hY)
  have : Epi v := hv.epi
  have : Mono v := by
    refine ⟨fun {W} a b hab => ?_⟩
    rw [← cancel_mono i, ← hw, ← Category.assoc, ← Category.assoc, hab]
  have : IsIso v := isIso_of_mono_of_epi v
  exact F.prop_of_iso (asIso v).symm hF'
end IsPretorsionTheory
end PretorsionImageClosed.Statement
