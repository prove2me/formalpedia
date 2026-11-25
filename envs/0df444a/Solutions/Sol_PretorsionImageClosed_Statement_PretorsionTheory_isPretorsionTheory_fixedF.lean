-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.isPretorsionTheory_fixedF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:52:36.94018+00:00
-- url     : https://prove2.me/submissions/395dfbf0-6290-413c-8238-943f8974baf8

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isSubobjectClosed_fixedF
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_F_le_fixedF
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_prop_of_meetT_fixedF
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrekernel
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_realization
public import Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_of_closed


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
variable (S : Set (PretorsionTheory C)) (Z : Subcategory C)
variable {S Z} {P₀ : PretorsionTheory C} (hP₀ : P₀ ∈ S) (hS : ∀ P ∈ S, P.middle = Z.prop)
include hP₀ hS
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution : IsPretorsionTheory (meetT S).prop (fixedF S Z).prop := by
  have hTm : (meetT S).IsQuotientClosed := isQuotientClosed_meetT S
  have hFz : (fixedF S Z).IsSubobjectClosed := isSubobjectClosed_fixedF hP₀ hS
  refine isPretorsionTheory_of_realization hTm hFz (fun Y => ?_) (fun E => ?_)
  · have ht : (meetT S).trace ((meetT S).trace Y : C) = ⊤ :=
      (trace_eq_top_iff hTm).2 ((meetT S).prop_trace Y)
    haveI : IsIso ((meetT S).trace ((meetT S).trace Y : C)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 ht
    exact ⟨fun h => ⟨(meetT S).prop_trace Y,
      Z.prop_of_iso (asIso ((meetT S).trace ((meetT S).trace Y : C)).arrow).symm h⟩,
      fun h => Z.prop_of_iso (asIso ((meetT S).trace ((meetT S).trace Y : C)).arrow) h.2⟩
  · refine ⟨fun hE {Y} f hY => isTrivial_of_closed hTm hFz f hE hY, fun hE => ?_⟩
    show (meetT S).prop E
    rw [meetT, iInf_prop_iff]
    intro P
    have hPF : P.1.F.IsSubobjectClosed := P.1.isPretorsionTheory.isSubobjectClosed
    obtain ⟨W, hW, g, k, hgk⟩ := hE (cokernel.π (P.1.F.reject E).arrow)
      (F_le_fixedF hS P.2 _ (P.1.F.prop_cokernel_reject E))
    have hWZ : Z.prop W := prop_of_meetT_fixedF hW.1 hW.2
    have hWP : (P.1.T.prop ⊓ P.1.F.prop) W := by
      have := hS P.1 P.2
      rw [PretorsionTheory.middle] at this
      rw [this]
      exact hWZ
    have htriv : IsTrivial (P.1.T.prop ⊓ P.1.F.prop) (𝟙 E ≫ cokernel.π (P.1.F.reject E).arrow) :=
      ⟨W, hWP, g, k, by rw [Category.id_comp, hgk]⟩
    obtain ⟨w, hw, -⟩ := (P.1.isPretorsionTheory.traceRejectCondition E).isPrekernel
      P.1.isPretorsionTheory.isQuotientClosed hPF |>.2 (𝟙 E) htriv
    exact P.1.T.prop_of_retract ⟨w, _, hw⟩ (P.1.T.prop_trace E)
end PretorsionImageClosed.Statement.PretorsionTheory
