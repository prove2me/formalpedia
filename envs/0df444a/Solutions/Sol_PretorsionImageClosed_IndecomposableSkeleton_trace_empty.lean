-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.trace_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:46:18.534909+00:00
-- url     : https://prove2.me/submissions/53fc1823-6004-4a14-bdd5-97d662ecc4d2

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
theorem _root_.solution (X : FGModuleCat.{w} R) :
    σ.trace ∅ X = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro f
  have hzero : f.map = 0 := by
    apply biproduct.hom_ext'
    intro t
    exact False.elim (f.mem t)
  rw [hzero]
  simp
end PretorsionImageClosed.IndecomposableSkeleton
