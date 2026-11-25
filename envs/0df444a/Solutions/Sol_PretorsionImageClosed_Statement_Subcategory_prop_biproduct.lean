-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_biproduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:41:27.711311+00:00
-- url     : https://prove2.me/submissions/acfed11e-be14-4486-bee5-9548dd79bffc

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biproduct_fin

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution {J : Type*} [Fintype J] (f : J → C) (h : ∀ j, Z.prop (f j)) :
    Z.prop (⨁ f) := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine Z.prop_of_iso (biproduct.whiskerEquiv e.symm (fun j => Iso.refl _)) ?_
  exact Z.prop_biproduct_fin _ fun j => h _
end PretorsionImageClosed.Statement.Subcategory
