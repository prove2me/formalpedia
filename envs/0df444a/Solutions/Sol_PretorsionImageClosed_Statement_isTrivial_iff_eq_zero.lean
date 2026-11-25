-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isTrivial_iff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:51:40.255184+00:00
-- url     : https://prove2.me/submissions/231f543f-462b-4e32-a4b8-61db3b7ed773

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_zero


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {Z : Subcategory C} (hZ : ∀ X, Z.prop X → IsZero X) {X Y : C}
    (f : X ⟶ Y) : IsTrivial Z.prop f ↔ f = 0 := by
  constructor
  · rintro ⟨W, hW, g, h, rfl⟩
    rw [(hZ W hW).eq_zero_of_src h, comp_zero]
  · rintro rfl
    exact ⟨0, Z.prop_zero, 0, 0, by rw [comp_zero]⟩
end PretorsionImageClosed.Statement
