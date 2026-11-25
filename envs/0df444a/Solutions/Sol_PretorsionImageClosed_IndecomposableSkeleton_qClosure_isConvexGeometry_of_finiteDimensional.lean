-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.qClosure_isConvexGeometry_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:30:15.617726+00:00
-- url     : https://prove2.me/submissions/3a101cb8-2560-4389-b70a-ec2998444d93

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange_of_finiteDimensional
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isClosed_empty


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
    σ.qClosure.IsConvexGeometry :=
  ⟨qClosure_isClosed_empty σ,
    qClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩
end PretorsionImageClosed.IndecomposableSkeleton
