-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.sClosure_isConvexGeometry_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:56:09.51745+00:00
-- url     : https://prove2.me/submissions/6d88fd41-c66e-49ce-9042-b3f82fa27cef

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange_of_finiteDimensional
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isClosed_empty


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
theorem _root_.solution
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.sClosure.IsConvexGeometry :=
  ⟨sClosure_isClosed_empty σ,
    sClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩
end PretorsionImageClosed.IndecomposableSkeleton
