-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.inSub_of_reject_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:42:30.900864+00:00
-- url     : https://prove2.me/submissions/a40767bd-bb0c-4ead-9258-ca05d50c4b7b

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_SelectedMapFrom_ker_flattenFinset_le
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_exists_finset_reject_eq
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective


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
    (hX : IsFiniteLength R X)
    (hreject : σ.reject S X = ⊥) :
    σ.InSub S X := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_reject_eq σ S X hX
  let f := SelectedMapFrom.flattenFinset σ F
  have hker_le :
      LinearMap.ker f.map.hom.hom ≤
        ⨅ g ∈ F, LinearMap.ker g.map.hom.hom := by
    rw [le_iInf_iff]
    intro g
    rw [le_iInf_iff]
    intro hg
    exact SelectedMapFrom.ker_flattenFinset_le σ F g hg
  have hker : LinearMap.ker f.map.hom.hom = ⊥ := by
    apply bot_unique
    rw [hF, hreject] at hker_le
    exact hker_le
  refine ⟨{
    index := f.index
    label := f.label
    mem := f.mem
    map := f.map
    mono := ?_ }⟩
  apply (FGModuleCat.mono_iff_injective f.map).mpr
  exact LinearMap.ker_eq_bot.mp hker
end PretorsionImageClosed.IndecomposableSkeleton
