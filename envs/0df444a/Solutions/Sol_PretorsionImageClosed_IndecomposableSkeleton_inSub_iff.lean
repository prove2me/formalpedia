-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inSub_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:34.777793+00:00
-- url     : https://prove2.me/submissions/392ed2a9-6f4f-4b5e-ba2c-76ea55c50be7

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inAdd_obj
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biproduct


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution (S : Set ι) (X : FGModuleCat.{w} R) :
    σ.InSub S X ↔ Statement.Cogen (σ.addOf S) X := by
  constructor
  · rintro ⟨P⟩
    letI : Fintype P.index := FintypeCat.fintype
    refine ⟨σ.sumOver P.index P.label, ?_, P.map, P.mono⟩
    exact (σ.addOf S).prop_biproduct _ fun t => inAdd_obj σ (P.mem t)
  · rintro ⟨Y, hY, i, hi⟩
    obtain ⟨P⟩ := hY
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := i ≫ P.iso.hom
      mono := mono_comp _ _ }⟩
end PretorsionImageClosed.IndecomposableSkeleton
