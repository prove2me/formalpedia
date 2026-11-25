-- Prove2me | solution 1 for PretorsionImageClosed.kernelSubobject_biprod_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:42.990694+00:00
-- url     : https://prove2.me/submissions/1ab1d875-03f2-4d4b-ac75-20290f4c98fe

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y₁ Y₂ : C} (f : X ⟶ Y₁) (g : X ⟶ Y₂) :
    kernelSubobject (biprod.lift f g) = kernelSubobject f ⊓ kernelSubobject g := by
  apply le_antisymm
  · apply le_inf
    · refine le_kernelSubobject _ _ ?_
      have h : (kernelSubobject (biprod.lift f g)).arrow ≫ f =
          ((kernelSubobject (biprod.lift f g)).arrow ≫ biprod.lift f g) ≫ biprod.fst := by
        rw [Category.assoc, biprod.lift_fst]
      rw [h, kernelSubobject_arrow_comp, zero_comp]
    · refine le_kernelSubobject _ _ ?_
      have h : (kernelSubobject (biprod.lift f g)).arrow ≫ g =
          ((kernelSubobject (biprod.lift f g)).arrow ≫ biprod.lift f g) ≫ biprod.snd := by
        rw [Category.assoc, biprod.lift_snd]
      rw [h, kernelSubobject_arrow_comp, zero_comp]
  · exact le_kernelSubobject _ _ (by
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, zero_comp,
          ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_left _ _), Category.assoc,
          kernelSubobject_arrow_comp, comp_zero]
      · rw [Category.assoc, biprod.lift_snd, zero_comp,
          ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_right _ _), Category.assoc,
          kernelSubobject_arrow_comp, comp_zero])
end PretorsionImageClosed
