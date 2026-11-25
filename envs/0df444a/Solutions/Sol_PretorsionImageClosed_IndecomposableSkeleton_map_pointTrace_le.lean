-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.map_pointTrace_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:23.140347+00:00
-- url     : https://prove2.me/submissions/2e4c6131-4975-40f1-bea3-847e567578ce

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange

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
theorem _root_.solution {i : ι}
    {X Y : FGModuleCat.{w} R} (f : X ⟶ Y) :
    Submodule.map f.hom.hom (σ.pointTrace i X) ≤
      σ.pointTrace i Y := by
  rw [pointTrace, Submodule.map_iSup]
  apply iSup_le
  intro g
  rw [← LinearMap.range_comp]
  exact le_iSup
    (fun h : σ.obj i ⟶ Y ↦ LinearMap.range h.hom.hom)
    (g ≫ f)
end PretorsionImageClosed.IndecomposableSkeleton
