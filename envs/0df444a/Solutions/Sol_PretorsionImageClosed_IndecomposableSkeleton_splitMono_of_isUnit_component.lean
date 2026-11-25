-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.splitMono_of_isUnit_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:15:32.326948+00:00
-- url     : https://prove2.me/submissions/bcdd7eaa-07de-4184-830c-65f4f76ac107

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isIso_iff_bijective


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
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (t : P.index) (ht : P.label t = x)
    (hunit :
      IsUnit
        ((P.map ≫
          biproduct.π
              (fun j : P.index ↦ σ.obj (P.label j)) t ≫
            eqToHom (congrArg σ.obj ht)).hom.hom)) :
    Nonempty (SplitMono P.map) := by
  let q : σ.obj (P.label t) ⟶ σ.obj x :=
    eqToHom (congrArg σ.obj ht)
  let a : σ.obj x ⟶ σ.obj x :=
    P.map ≫
      biproduct.π
          (fun j : P.index ↦ σ.obj (P.label j)) t ≫ q
  have hbijective : Function.Bijective a.hom.hom :=
    (Module.End.isUnit_iff a.hom.hom).mp hunit
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (F.map a) := by
    change IsIso a.hom
    exact
      (ConcreteCategory.isIso_iff_bijective a.hom).mpr
        hbijective
  letI : IsIso a :=
    isIso_of_reflects_iso a F
  refine ⟨{
    retraction :=
      biproduct.π
          (fun j : P.index ↦ σ.obj (P.label j)) t ≫
        q ≫ inv a
    id := ?_ }⟩
  change a ≫ inv a = 𝟙 _
  exact IsIso.hom_inv_id a
end PretorsionImageClosed.IndecomposableSkeleton
