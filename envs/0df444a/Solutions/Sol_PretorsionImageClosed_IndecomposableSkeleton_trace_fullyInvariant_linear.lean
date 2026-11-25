-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_fullyInvariant_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:14:54.832044+00:00
-- url     : https://prove2.me/submissions/d49e120b-5867-4129-af17-20c7af2ad209

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_fullyInvariant


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
    Submodule.map f (σ.trace S X) ≤ σ.trace S X := by
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  let fc : X ⟶ X := F.preimage (ModuleCat.ofHom f)
  have hfc : fc.hom.hom = f := by
    have h := F.map_preimage (ModuleCat.ofHom f)
    exact congrArg ModuleCat.Hom.hom h
  rw [← hfc]
  exact trace_fullyInvariant σ X fc
end PretorsionImageClosed.IndecomposableSkeleton
