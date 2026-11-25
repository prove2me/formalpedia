-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_iInf_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:25:52.229+00:00
-- url     : https://prove2.me/submissions/b4a95f06-df4a-4bf6-9d2a-e42aa23f4453

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_trace
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_left
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
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
namespace PretorsionImageClosed.Statement
theorem _root_.solution {ι : Type*} {T F : ι → Subcategory C} {T'' F'' : Subcategory C}
    (h : ∀ i, IsPretorsionTheory (T i).prop (F i).prop) (h'' : IsPretorsionTheory T''.prop F''.prop)
    (hT : ∀ i, T'' ≤ T i) (hF : ∀ i, F i ≤ F'') :
    IsPretorsionTheory (Subcategory.iInf T).prop F''.prop := by
  have hTq : (Subcategory.iInf T).IsQuotientClosed :=
    IsQuotientClosed.iInf fun i => (h i).isQuotientClosed
  have hF'' : F''.IsSubobjectClosed := h''.isSubobjectClosed
  refine isPretorsionTheory_of_realization hTq hF'' (fun Y => ?_) (fun E => ?_)
  · refine ⟨fun hY => ⟨(Subcategory.iInf T).prop_trace Y,
      hF'' ((Subcategory.iInf T).trace Y).arrow inferInstance hY⟩, fun hZ => ?_⟩
    -- `t''(Y) ⊆ t̂(Y) ∈ F''`
    have hle : T''.trace Y ≤ (Subcategory.iInf T).trace Y := by
      apply le_trace hTq
      rw [iInf_prop_iff]
      exact fun i => hT i _ (T''.prop_trace Y)
    exact (h''.prop_iff_prop_trace Y).2
      ⟨T''.prop_trace Y, hF'' (Subobject.ofLE _ _ hle) inferInstance hZ.2⟩
  · refine ⟨fun hE {Y} f hY => isTrivial_of_closed hTq hF'' f hE hY, fun hE => ?_⟩
    rw [iInf_prop_iff]
    intro i
    have hFi : (F i).IsSubobjectClosed := (h i).isSubobjectClosed
    obtain ⟨W, hW, g, k, hgk⟩ := hE (cokernel.π ((F i).reject E).arrow)
      (hF i _ ((F i).prop_cokernel_reject E))
    have hWi : (T i).prop W := (iInf_prop_iff T W).1 hW.1 i
    have htriv : IsTrivial ((T i).prop ⊓ (F i).prop) (𝟙 E ≫ cokernel.π ((F i).reject E).arrow) := by
      rw [Category.id_comp, ← hgk]
      exact (isTrivial_of_closed (h i).isQuotientClosed hFi k hWi
        ((F i).prop_cokernel_reject E)).comp_left g
    obtain ⟨w, hw, -⟩ := ((h i).traceRejectCondition E).isPrekernel (h i).isQuotientClosed hFi |>.2
      (𝟙 E) htriv
    exact (T i).prop_of_retract ⟨w, _, hw⟩ ((T i).prop_trace E)
end PretorsionImageClosed.Statement
