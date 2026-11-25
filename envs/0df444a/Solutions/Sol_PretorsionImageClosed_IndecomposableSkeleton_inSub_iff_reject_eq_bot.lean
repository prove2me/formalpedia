-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inSub_iff_reject_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:57.624358+00:00
-- url     : https://prove2.me/submissions/2a0368b9-b210-4c6c-897a-a47ced800142

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_inSub_of_reject_eq_bot
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_eq_bot_of_inSub

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X) :
    σ.InSub S X ↔ σ.reject S X = ⊥ :=
  ⟨reject_eq_bot_of_inSub σ S X,
    inSub_of_reject_eq_bot σ S X hX⟩
end PretorsionImageClosed.IndecomposableSkeleton
