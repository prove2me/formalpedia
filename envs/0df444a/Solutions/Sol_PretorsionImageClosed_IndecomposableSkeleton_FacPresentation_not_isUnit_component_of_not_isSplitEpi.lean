-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.not_isUnit_component_of_not_isSplitEpi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:29.83626+00:00
-- url     : https://prove2.me/submissions/d92a2272-95f5-48e4-a0ca-9797322a4845

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_isSplitEpi_of_isUnit_component

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
open PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
namespace PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
theorem _root_.solution
    {S : Set ι} {x : ι}
    (P : σ.FacPresentation S (σ.obj x))
    (hP : ¬ IsSplitEpi P.map)
    (t : P.index) (ht : P.label t = x) :
    ¬ IsUnit
      ((eqToHom (congrArg σ.obj ht.symm) ≫
        P.component σ t).hom.hom) :=
  fun hunit ↦ hP (P.isSplitEpi_of_isUnit_component σ t ht hunit)
end PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
