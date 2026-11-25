-- Prove2me | solution 1 for PretorsionImageClosed.IndecomposableSkeleton.pointTrace_le_trace_sup_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:34:43.908142+00:00
-- url     : https://prove2.me/submissions/a939ab7d-dd7f-4c58-9356-cb1df376220b

module
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_QuotientAntiExchange
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_comp_mem_end_jacobson
public import Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_map_trace_le_trace
public import Theorems.Thm_PretorsionImageClosed_range_le_idealRange


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
    (C : Set ι) {x y : ι} (hxy : x ≠ y)
    (hY :
      σ.trace C (σ.obj y) ⊔
        σ.pointTrace x (σ.obj y) = ⊤) :
    σ.pointTrace y (σ.obj x) ≤
      σ.trace C (σ.obj x) ⊔
        PretorsionImageClosed.idealRange
          (Ring.jacobson (Module.End R (σ.obj x))) := by
  apply iSup_le
  intro f
  rw [← Submodule.map_top, ← hY, Submodule.map_sup]
  apply sup_le_sup
  · exact map_trace_le_trace σ f
  · rw [pointTrace, Submodule.map_iSup]
    apply iSup_le
    intro g
    rw [← LinearMap.range_comp]
    exact PretorsionImageClosed.range_le_idealRange _
      (comp_mem_end_jacobson σ hxy f g)
end PretorsionImageClosed.IndecomposableSkeleton
