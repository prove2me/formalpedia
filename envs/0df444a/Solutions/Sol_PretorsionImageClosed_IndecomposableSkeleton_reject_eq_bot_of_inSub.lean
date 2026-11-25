-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.reject_eq_bot_of_inSub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:04:34.954361+00:00
-- url     : https://prove2.me/submissions/6def936a-d9b3-44c2-b998-a695f64f704b

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_ker
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_ker_eq_bot_of_mono


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
    (hsub : σ.InSub S X) :
    σ.reject S X = ⊥ := by
  obtain ⟨P⟩ := hsub
  let f : σ.SelectedMapFrom S X :=
    { index := P.index
      label := P.label
      mem := P.mem
      map := P.map }
  letI : Mono P.map := P.mono
  apply bot_unique
  exact (reject_le_ker σ f).trans
    (le_of_eq (FGModuleCat.ker_eq_bot_of_mono P.map))
end PretorsionImageClosed.IndecomposableSkeleton
