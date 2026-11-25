-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.qClosure_isAntiExchange_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:14:14.523463+00:00
-- url     : https://prove2.me/submissions/d6e01750-a43c-4b6b-85ab-fe39564376ae

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_moduleEnd_of_finiteDimensional


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
    σ.qClosure.IsAntiExchange := by
  letI : ∀ i : ι,
      IsArtinianRing (Module.End R (σ.obj i)) :=
    fun i ↦
      PretorsionImageClosed.isArtinianRing_moduleEnd_of_finiteDimensional
        (K := K) (B := R) (M := σ.obj i)
  exact qClosure_isAntiExchange σ
end PretorsionImageClosed.IndecomposableSkeleton
