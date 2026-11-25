-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPretorsionTheory.isQuotientClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:18.611658+00:00
-- url     : https://prove2.me/submissions/a535da2e-ec12-4212-ad8f-1c99b65bb244

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_of_isIso


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
    (h : IsPretorsionTheory T.prop F.prop) : T.IsQuotientClosed := by
  intro X Y q hq hX
  obtain ⟨T', F', u, v, hT', hF', hu, hv⟩ := h.2 Y
  -- `q ≫ v` is trivial, so `q` factors through the prekernel `u`
  obtain ⟨w, hw, -⟩ := hu.2 q (h.1 (q ≫ v) hX hF')
  have : Mono u := hu.mono
  have : Epi u := by
    refine ⟨fun {W} a b hab => ?_⟩
    rw [← cancel_epi q, ← hw, Category.assoc, Category.assoc, hab]
  have : IsIso u := isIso_of_mono_of_epi u
  exact T.prop_of_isIso u hT'
end IsPretorsionTheory
end PretorsionImageClosed.Statement
