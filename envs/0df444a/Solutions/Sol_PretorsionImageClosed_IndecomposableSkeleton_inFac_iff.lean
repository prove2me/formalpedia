-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inFac_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:30.821622+00:00
-- url     : https://prove2.me/submissions/0d586352-8d17-49de-8027-87dba07606e1

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Definitions.Def_PretorsionImageClosed_Subcategories_Biproducts
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Subcategories
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inAdd_obj
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
    σ.InFac S X ↔ Statement.Gen (σ.addOf S) X := by
  constructor
  · rintro ⟨P⟩
    letI : Fintype P.index := FintypeCat.fintype
    refine ⟨σ.sumOver P.index P.label, ?_, P.map, P.epi⟩
    exact (σ.addOf S).prop_biproduct _ fun t => inAdd_obj σ (P.mem t)
  · rintro ⟨Y, hY, p, hp⟩
    obtain ⟨P⟩ := hY
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := P.iso.inv ≫ p
      epi := epi_comp _ _ }⟩
end PretorsionImageClosed.IndecomposableSkeleton
