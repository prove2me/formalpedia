-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.isRelativeSplitProjective_of_not_mem_qClosure_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:01.588635+00:00
-- url     : https://prove2.me/submissions/8ba356cc-131c-474b-ba2f-6cd2d9712e13

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_SplitProjective
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_FacPresentation_range_le_trace_sdiff_sup_idealRange
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_range_eq_top_of_epi
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_trace_eq_top
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_sClosure_iff_inSub
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_qSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_reject_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_sSet_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_empty
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_trace_fullyInvariant_linear
public import Theorems.Thm_PretorsionImageClosed_eq_top_of_nilpotent_idealRange
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
namespace PretorsionImageClosed.IndecomposableSkeleton
theorem _root_.solution
    (C : Set ι) (x : ι)
    [IsArtinianRing (Module.End R (σ.obj x))]
    (hx : x ∉ σ.qClosure (C \ {x})) :
    σ.IsRelativeSplitProjective C x := by
  intro P
  by_contra hP
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hsup :
      σ.trace (C \ {x}) (σ.obj x) ⊔
        PretorsionImageClosed.idealRange J = ⊤ := by
    letI : Epi P.map := P.epi
    apply top_unique
    rw [← FGModuleCat.range_eq_top_of_epi P.map]
    exact P.range_le_trace_sdiff_sup_idealRange σ hP
  have htrace : σ.trace (C \ {x}) (σ.obj x) = ⊤ := by
    apply PretorsionImageClosed.eq_top_of_nilpotent_idealRange J
    · exact trace_fullyInvariant_linear σ (σ.obj x)
    · dsimp only [J]
      exact
        (Ideal.jacobson_bot (R :=
          Module.End R (σ.obj x))) ▸
            IsArtinianRing.isNilpotent_jacobson_bot
    · exact hsup
  exact hx ((mem_qClosure_iff_trace_eq_top σ (C \ {x}) x).2 htrace)
end PretorsionImageClosed.IndecomposableSkeleton
