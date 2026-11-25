-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPretorsionTheory.prop_iff_prop_cokernel_reject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:16.891912+00:00
-- url     : https://prove2.me/submissions/e0ff869b-f134-415a-a927-843288036678

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff
public import Theorems.Thm_PretorsionImageClosed_epi_of_imageSubobject_eq_top
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_eq_top_of_epi


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (T F : Subcategory C) (X : C)
variable {T F X}
variable (hP : IsPretorsionTheory T.prop F.prop)
include hP
namespace PretorsionImageClosed.Statement
namespace IsPretorsionTheory
theorem _root_.solution (X : C) :
    T.prop X ↔ (T.prop ⊓ F.prop) (cokernel (F.reject X).arrow) := by
  have hT : T.IsQuotientClosed := hP.isQuotientClosed
  have hc := hP.traceRejectCondition X
  constructor
  · intro hX
    refine ⟨?_, F.prop_cokernel_reject X⟩
    rw [← trace_eq_top_iff hT, hc.trace_cokernel]
    have ht : T.trace X = ⊤ := (trace_eq_top_iff hT).2 hX
    rw [ht]
    haveI : IsIso (⊤ : Subobject X).arrow := inferInstance
    exact imageSubobject_eq_top_of_epi _
  · intro hQ
    have ht : T.trace (cokernel (F.reject X).arrow) = ⊤ := (trace_eq_top_iff hT).2 hQ.1
    rw [hc.trace_cokernel] at ht
    haveI : Epi ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) := epi_of_imageSubobject_eq_top _ ht
    -- `t(X) → X` is then an epimorphism, hence an isomorphism
    have hk : kernel.ι (cokernel.π (F.reject X).arrow) ≫ cokernel.π (T.trace X).arrow = 0 := by
      have hle : kernelSubobject (cokernel.π (F.reject X).arrow) ≤
          kernelSubobject (cokernel.π (T.trace X).arrow) :=
        (kernelSubobject_cokernel_π_arrow _).le.trans
          (hc.reject_le_trace.trans (kernelSubobject_cokernel_π_arrow _).ge)
      rw [← kernelSubobject_arrow', Category.assoc, (Subobject.le_kernelSubobject_iff _ _).1 hle,
        comp_zero]
    have he : Abelian.epiDesc (cokernel.π (F.reject X).arrow) _ hk = 0 := by
      rw [← cancel_epi ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)), Category.assoc, Abelian.comp_epiDesc,
        cokernel.condition, comp_zero]
    have hc0 : cokernel.π (T.trace X).arrow = 0 := by
      rw [← Abelian.comp_epiDesc (cokernel.π (F.reject X).arrow) _ hk, he, comp_zero]
    haveI : Epi (T.trace X).arrow := Abelian.epi_of_cokernel_π_eq_zero _ hc0
    haveI : IsIso (T.trace X).arrow := isIso_of_mono_of_epi _
    rw [← trace_eq_top_iff hT, ← Subobject.isIso_arrow_iff_eq_top]
    infer_instance
end IsPretorsionTheory
end PretorsionImageClosed.Statement
