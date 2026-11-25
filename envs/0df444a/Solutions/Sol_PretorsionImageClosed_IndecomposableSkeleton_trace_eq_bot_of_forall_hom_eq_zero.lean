-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_eq_bot_of_forall_hom_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:19:14.959001+00:00
-- url     : https://prove2.me/submissions/051f2cce-f08f-406f-8e63-bd410f4f883c

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces

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
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hzero : ∀ i : ι, i ∈ S → ∀ f : σ.obj i ⟶ X, f = 0) :
    σ.trace S X = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro f
  have hmap : f.map = 0 := by
    apply biproduct.hom_ext'
    intro t
    simpa using hzero (f.label t) (f.mem t)
      (biproduct.ι (fun t : f.index ↦ σ.obj (f.label t)) t ≫ f.map)
  rw [hmap]
  simp
end PretorsionImageClosed.IndecomposableSkeleton
