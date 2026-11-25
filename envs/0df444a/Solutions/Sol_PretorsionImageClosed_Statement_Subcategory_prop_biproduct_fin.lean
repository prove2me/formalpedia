-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_biproduct_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:37:04.673943+00:00
-- url     : https://prove2.me/submissions/4193b783-6271-4620-80dd-5a9039058263

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts

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
theorem _root_.solution : ∀ {n : ℕ} (f : Fin n → C), (∀ j, Z.prop (f j)) → Z.prop (⨁ f)
  | 0, f, _ => Z.prop_of_isZero (by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext'
      intro j
      exact j.elim0)
  | n + 1, f, h => Z.prop_of_iso (biproductFinSuccIso f).symm
      (Z.prop_biprod (h 0) (solution _ fun j => h j.succ))
end PretorsionImageClosed.Statement.Subcategory
