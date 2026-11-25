-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:23.372309+00:00
-- url     : https://prove2.me/submissions/7dfc00a1-af75-4058-93eb-6534f4c64d03

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_length_cokernel_lt
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_quotient_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_inf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsQuotientClosed_inf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsSubobjectClosed_inf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_prop


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {T F₁ F₂ : Subcategory C} (h₁ : IsPretorsionTheory T.prop F₁.prop)
    (h₂ : IsPretorsionTheory T.prop F₂.prop) : IsPretorsionTheory T.prop (F₁ ⊓ F₂).prop := by
  have hT : T.IsQuotientClosed := h₁.isQuotientClosed
  have hF₁ : F₁.IsSubobjectClosed := h₁.isSubobjectClosed
  have hF₂ : F₂.IsSubobjectClosed := h₂.isSubobjectClosed
  have hG : (F₁ ⊓ F₂).IsSubobjectClosed := hF₁.inf hF₂
  have key : ∀ (n : ℕ) (X : C), length X = n → TraceRejectCondition T (F₁ ⊓ F₂) X := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hX
      by_cases hr₁ : F₁.reject X = ⊥
      · by_cases hr₂ : F₂.reject X = ⊥
        · exact traceRejectCondition_of_prop hT hG
            ⟨(reject_eq_bot_iff hF₁).1 hr₁, (reject_eq_bot_iff hF₂).1 hr₂⟩
        · exact traceRejectCondition_of_quotient_reject hT hF₂ hG (fun _ h => h.2)
            (h₂.traceRejectCondition X) (ih _ (hX ▸ length_cokernel_lt hr₂) _ rfl)
      · exact traceRejectCondition_of_quotient_reject hT hF₁ hG (fun _ h => h.1)
          (h₁.traceRejectCondition X) (ih _ (hX ▸ length_cokernel_lt hr₁) _ rfl)
  exact isPretorsionTheory_of_traceRejectCondition hT hG fun X => key _ X rfl
end PretorsionImageClosed.Statement
