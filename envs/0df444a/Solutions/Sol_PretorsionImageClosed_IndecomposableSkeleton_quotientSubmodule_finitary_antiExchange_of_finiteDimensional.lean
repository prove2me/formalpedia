-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.quotientSubmodule_finitary_antiExchange_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:49.676073+00:00
-- url     : https://prove2.me/submissions/29d2ec57-6ea4-497c-842d-93d241495a67

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isAntiExchange_of_finiteDimensional
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isAntiExchange_of_finiteDimensional
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qClosure_isFinitary
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sClosure_isFinitary


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
    (σ.qClosure.IsFinitary ∧ σ.qClosure.IsAntiExchange) ∧
      (σ.sClosure.IsFinitary ∧ σ.sClosure.IsAntiExchange) :=
  ⟨⟨qClosure_isFinitary σ,
      qClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩,
    ⟨sClosure_isFinitary σ,
      sClosure_isAntiExchange_of_finiteDimensional (K := K) σ⟩⟩
end PretorsionImageClosed.IndecomposableSkeleton
