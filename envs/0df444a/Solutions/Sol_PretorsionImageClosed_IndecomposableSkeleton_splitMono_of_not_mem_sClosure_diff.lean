-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.splitMono_of_not_mem_sClosure_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:33.075131+00:00
-- url     : https://prove2.me/submissions/8e8c32f3-299f-484f-92bc-567a217f00d4

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SubmoduleAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitInjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_splitMono_of_isUnit_component
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_ker_eq_bot_of_mono
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_reject_eq_bot
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_fullyInvariant_linear
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_le_ker_of_mem
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_eq_bot_of_inf_idealKernel
public import Theorems.Thm_PretorsionImageClosed_idealKernel_bot
public import Theorems.Thm_PretorsionImageClosed_idealKernel_le_ker
public import Theorems.Thm_PretorsionImageClosed_idealKernel_top
public import Theorems.Thm_PretorsionImageClosed_idealRange_bot
public import Theorems.Thm_PretorsionImageClosed_idealRange_top
public import Theorems.Thm_PretorsionImageClosed_mem_endNonunitsIdeal_iff
public import Theorems.Thm_PretorsionImageClosed_mem_end_jacobson_iff_not_isUnit
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


section
@[expose] public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
omit [IsNoetherianRing R] in
private theorem biproduct_apply_eq_zero_of_components
    {J : Type*} [Fintype J]
    {X : FGModuleCat.{w} R} {Y : J → FGModuleCat.{w} R}
    (g : X ⟶ ⨁ Y) (x : X)
    (h : ∀ j, (g ≫ biproduct.π Y j).hom.hom x = 0) :
    g.hom.hom x = 0 := by
  classical
  let C : Submodule R X := R ∙ x
  letI : Module.Finite R C :=
    Module.Finite.of_fg (Submodule.fg_span_singleton x)
  let e : FGModuleCat.of R C ⟶ X :=
    FGModuleCat.ofHom C.subtype
  have he : e ≫ g = 0 := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, zero_comp]
    apply FGModuleCat.hom_ext
    ext z
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp z.2
    change (g ≫ biproduct.π Y j).hom.hom z.1 = 0
    rw [← hr, map_smul, h j, smul_zero]
  let z : C := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hz := congrArg
    (fun f : FGModuleCat.of R C ⟶ ⨁ Y ↦ f.hom.hom z) he
  change g.hom.hom (C.subtype z) = 0 at hz
  exact hz
end PretorsionImageClosed.IndecomposableSkeleton
end
end
end

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
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (hnot : x ∉ σ.sClosure (C \ {x}))
    (P : σ.SubPresentation C (σ.obj x)) :
    Nonempty (SplitMono P.map) := by
  classical
  by_contra hnosplit
  let D : Set ι := C \ {x}
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have component_mem_J
      (t : P.index) (ht : P.label t = x) :
      ((P.map ≫
        biproduct.π
            (fun j : P.index ↦ σ.obj (P.label j)) t ≫
          eqToHom (congrArg σ.obj ht)).hom.hom) ∈ J := by
    apply
      (PretorsionImageClosed.mem_end_jacobson_iff_not_isUnit
        (σ.indecomposable x) (σ.finiteLength x) _).2
    intro hunit
    exact hnosplit
      (splitMono_of_isUnit_component σ P t ht hunit)
  have hinf :
      σ.reject D (σ.obj x) ⊓
          PretorsionImageClosed.idealKernel J =
        ⊥ := by
    apply le_antisymm
    · intro z hz
      letI : Fintype P.index := FintypeCat.fintype
      have hmapzero : P.map.hom.hom z = 0 := by
        apply biproduct_apply_eq_zero_of_components P.map z
        intro t
        let ft : σ.obj x ⟶ σ.obj (P.label t) :=
          P.map ≫
            biproduct.π
              (fun j : P.index ↦ σ.obj (P.label j)) t
        by_cases ht : P.label t = x
        · let q : σ.obj (P.label t) ⟶ σ.obj x :=
            eqToHom (congrArg σ.obj ht)
          let a : Module.End R (σ.obj x) :=
            (ft ≫ q).hom.hom
          have haJ : a ∈ J := by
            exact component_mem_J t ht
          have hazero :=
            PretorsionImageClosed.idealKernel_le_ker a haJ hz.2
          rw [LinearMap.mem_ker] at hazero
          have hqinjective : Function.Injective q.hom.hom :=
            (FGModuleCat.mono_iff_injective q).mp inferInstance
          apply hqinjective
          simpa only [a, q, ft, FGModuleCat.hom_hom_comp,
            LinearMap.comp_apply, map_zero] using hazero
        · have htD : P.label t ∈ D := by
            refine ⟨P.mem t, ?_⟩
            simpa only [Set.mem_singleton_iff] using ht
          exact LinearMap.mem_ker.mp
            (reject_le_ker_of_mem σ htD ft hz.1)
      letI : Mono P.map := P.mono
      have hzker :
          z ∈ LinearMap.ker P.map.hom.hom :=
        LinearMap.mem_ker.mpr hmapzero
      rw [FGModuleCat.ker_eq_bot_of_mono P.map] at hzker
      exact hzker
    · exact bot_le
  have hreject : σ.reject D (σ.obj x) = ⊥ := by
    apply PretorsionImageClosed.eq_bot_of_inf_idealKernel J
    · exact reject_fullyInvariant_linear σ (σ.obj x)
    · dsimp only [J]
      exact
        (Ideal.jacobson_bot (R :=
          Module.End R (σ.obj x))) ▸
            IsArtinianRing.isNilpotent_jacobson_bot
    · exact hinf
  apply hnot
  exact (mem_sClosure_iff_reject_eq_bot σ D x).2 hreject
end PretorsionImageClosed.IndecomposableSkeleton
