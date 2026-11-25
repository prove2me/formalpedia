-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.comp_mem_end_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:11.511817+00:00
-- url     : https://prove2.me/submissions/c21119d4-7b99-40d5-b792-d59bd9c738c6

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_mem_end_jacobson_iff_not_isUnit
public import Theorems.Thm_PretorsionImageClosed_nonempty_linearEquiv_of_isUnit_comp


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
theorem _root_.solution {x y : ι} (hxy : x ≠ y)
    (f : σ.obj y ⟶ σ.obj x) (g : σ.obj x ⟶ σ.obj y) :
    f.hom.hom.comp g.hom.hom ∈
      Ring.jacobson (Module.End R (σ.obj x)) := by
  apply
    (PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
      (σ.indecomposable x) (σ.finiteLength x)
      (f.hom.hom.comp g.hom.hom)).2
  intro hunit
  obtain ⟨e⟩ :=
    PretorsionImageClosed.nonempty_linearEquiv_of_isUnit_comp
      (σ.indecomposable x) (σ.indecomposable y)
      f.hom.hom g.hom.hom hunit
  exact hxy (σ.eq_of_iso ⟨e.toFGModuleCatIso⟩)
end PretorsionImageClosed.IndecomposableSkeleton
