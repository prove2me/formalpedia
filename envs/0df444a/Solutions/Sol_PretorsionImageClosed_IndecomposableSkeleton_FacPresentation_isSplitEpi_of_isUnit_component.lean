-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.FacPresentation.isSplitEpi_of_isUnit_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:30:49.436379+00:00
-- url     : https://prove2.me/submissions/7aeb585a-3e7a-48b6-a898-b582db859008

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.mem_sClosure_iff_inSub
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.qSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.reject_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.sSet_empty
attribute [local simp] PretorsionImageClosed.IndecomposableSkeleton.trace_empty
attribute [local simp] PretorsionImageClosed.idealKernel_bot
attribute [local simp] PretorsionImageClosed.idealKernel_top
attribute [local simp] PretorsionImageClosed.idealRange_bot
attribute [local simp] PretorsionImageClosed.idealRange_top
attribute [local simp] PretorsionImageClosed.mem_endNonunitsIdeal_iff



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
open PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
namespace PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
theorem _root_.solution
    {S : Set ι} {x : ι}
    (P : σ.FacPresentation S (σ.obj x)) (t : P.index)
    (ht : P.label t = x)
    (hunit :
      IsUnit
        ((eqToHom (congrArg σ.obj ht.symm) ≫
          P.component σ t).hom.hom)) :
    IsSplitEpi P.map := by
  let a : Module.End R (σ.obj x) :=
    (eqToHom (congrArg σ.obj ht.symm) ≫
      P.component σ t).hom.hom
  let e : σ.obj x ≃ₗ[R] σ.obj x :=
    { toLinearMap := a
      invFun := (Equiv.ofBijective a
        ((Module.End.isUnit_iff a).mp hunit)).invFun
      left_inv := (Equiv.ofBijective a
        ((Module.End.isUnit_iff a).mp hunit)).left_inv
      right_inv := (Equiv.ofBijective a
        ((Module.End.isUnit_iff a).mp hunit)).right_inv }
  let s : σ.obj x ⟶ σ.sumOver P.index P.label :=
    FGModuleCat.ofHom e.symm.toLinearMap ≫
      eqToHom (congrArg σ.obj ht.symm) ≫
        biproduct.ι (fun t : P.index ↦ σ.obj (P.label t)) t
  have hinv :
      FGModuleCat.ofHom e.symm.toLinearMap ≫
          (eqToHom (congrArg σ.obj ht.symm) ≫
            P.component σ t) =
        𝟙 (σ.obj x) := by
    apply FGModuleCat.hom_ext
    ext z
    change
      ((eqToHom (congrArg σ.obj ht.symm) ≫
        P.component σ t).hom.hom) (e.symm z) = z
    change a (e.symm z) = z
    change e (e.symm z) = z
    exact e.apply_symm_apply z
  apply IsSplitEpi.mk'
  refine { section_ := s, id := ?_ }
  calc
    s ≫ P.map =
        FGModuleCat.ofHom e.symm.toLinearMap ≫
          (eqToHom (congrArg σ.obj ht.symm) ≫
            P.component σ t) := by
      dsimp only [s, component]
      simp only [Category.assoc]
    _ = 𝟙 (σ.obj x) := hinv
end PretorsionImageClosed.IndecomposableSkeleton.FacPresentation
