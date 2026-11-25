-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:27:41.650396+00:00
-- url     : https://prove2.me/submissions/eec58fe3-2029-46e7-bc8a-9d1f7fe051e6

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_of_reject_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_finInf
public import Theorems.Thm_PretorsionImageClosed_Statement_isSubobjectClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_exists_reject_finInf_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_traceRejectCondition
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_traceRejectCondition


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable {ι : Type*} (F : ι → Subcategory C)
variable {F} {T : Subcategory C} (hT : T.IsQuotientClosed) (h : ∀ i, IsPretorsionTheory T.prop (F i).prop)
include hT h
namespace PretorsionImageClosed.Statement
theorem _root_.solution : IsPretorsionTheory T.prop (Subcategory.iInf F).prop := by
  classical
  refine isPretorsionTheory_of_traceRejectCondition hT (isSubobjectClosed_iInf h) fun X => ?_
  obtain ⟨J₀, hJ₀⟩ := exists_reject_finInf_eq h X
  obtain ⟨J₁, hJ₁⟩ := exists_reject_finInf_eq h (T.trace X : C)
  have hc := (isPretorsionTheory_finInf hT h (J₀ ∪ J₁)).traceRejectCondition X
  exact hc.of_reject_eq (hJ₀ _ Finset.subset_union_left).symm
    (hJ₁ _ Finset.subset_union_right).symm
end PretorsionImageClosed.Statement
