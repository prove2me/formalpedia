-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.twoConvexGeometries_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:56.551398+00:00
-- url     : https://prove2.me/submissions/369bb09a-fa60-459c-9c03-a8e8eb641841

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isConvexGeometry_of_finiteDimensional
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isConvexGeometry_of_finiteDimensional


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
    [Finite ι]
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)] :
    σ.qClosure.IsConvexGeometry ∧
      σ.sClosure.IsConvexGeometry :=
  ⟨qClosure_isConvexGeometry_of_finiteDimensional (K := K) σ,
    sClosure_isConvexGeometry_of_finiteDimensional (K := K) σ⟩
end PretorsionImageClosed.IndecomposableSkeleton
