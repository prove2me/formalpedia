-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_cokernel_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:43:50.93989+00:00
-- url     : https://prove2.me/submissions/903d8dc6-d903-417d-9975-311cdfbd9f80

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hF : F.IsSubobjectClosed) {K K' : Subobject X}
    (hK : F.prop (cokernel K.arrow)) (hK' : F.prop (cokernel K'.arrow)) :
    F.prop (cokernel (K ⊓ K').arrow) := by
  let φ : X ⟶ cokernel K.arrow ⊞ cokernel K'.arrow :=
    biprod.lift (cokernel.π K.arrow) (cokernel.π K'.arrow)
  have hzero : (K ⊓ K').arrow ≫ φ = 0 := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, zero_comp,
        ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_left K K'),
        Category.assoc, cokernel.condition, comp_zero]
    · rw [Category.assoc, biprod.lift_snd, zero_comp,
        ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_right K K'),
        Category.assoc, cokernel.condition, comp_zero]
  have hker : ∀ (L : Subobject X), kernelSubobject (cokernel.π L.arrow) = L := fun L => by
    rw [← (ShortComplex.exact_iff_image_eq_kernel _).1 (ShortComplex.exact_cokernel L.arrow)]
    change imageSubobject L.arrow = L
    rw [imageSubobject_mono, Subobject.mk_arrow]
  have hexact : (ShortComplex.mk (K ⊓ K').arrow φ hzero).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject (K ⊓ K').arrow = kernelSubobject φ
    rw [imageSubobject_mono, Subobject.mk_arrow]
    apply le_antisymm
    · exact le_kernelSubobject _ _ hzero
    · apply le_inf
      · exact (le_kernelSubobject _ _ (by
          rw [← biprod.lift_fst (cokernel.π K.arrow) (cokernel.π K'.arrow), ← Category.assoc,
            kernelSubobject_arrow_comp, zero_comp])).trans_eq (hker K)
      · exact (le_kernelSubobject _ _ (by
          rw [← biprod.lift_snd (cokernel.π K.arrow) (cokernel.π K'.arrow), ← Category.assoc,
            kernelSubobject_arrow_comp, zero_comp])).trans_eq (hker K')
  have hmono := hexact.mono_cokernelDesc
  exact hF _ hmono (F.prop_biprod hK hK')
end PretorsionImageClosed.Statement.Subcategory
