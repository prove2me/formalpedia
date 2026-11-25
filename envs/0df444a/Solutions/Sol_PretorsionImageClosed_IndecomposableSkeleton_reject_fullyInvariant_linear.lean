-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_fullyInvariant_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:15:48.168182+00:00
-- url     : https://prove2.me/submissions/811adfe9-f048-4858-886a-cfeea8ee4aca

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_fullyInvariant


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
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution {S : Set ι}
    (X : FGModuleCat.{w} R) (f : Module.End R X) :
    Submodule.map f (σ.reject S X) ≤ σ.reject S X := by
  rw [Submodule.map_le_iff_le_comap]
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  let fc : X ⟶ X := F.preimage (ModuleCat.ofHom f)
  have hfc : fc.hom.hom = f := by
    have h := F.map_preimage (ModuleCat.ofHom f)
    exact congrArg ModuleCat.Hom.hom h
  rw [← hfc]
  exact reject_fullyInvariant σ X fc
end PretorsionImageClosed.IndecomposableSkeleton
