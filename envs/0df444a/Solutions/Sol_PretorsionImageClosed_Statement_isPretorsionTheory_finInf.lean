-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isPretorsionTheory_finInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:22:39.038565+00:00
-- url     : https://prove2.me/submissions/f99e4304-3780-4446-829e-083b4a095017

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_top_right
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_inf
public import Theorems.Thm_PretorsionImageClosed_Statement_finInf_prop_iff

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
theorem _root_.solution (J : Finset ι) : IsPretorsionTheory T.prop (finInf F J).prop := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have : (finInf F ∅).prop = (⊤ : Subcategory C).prop := by
      funext X
      apply propext
      rw [finInf_prop_iff]
      exact ⟨fun _ => trivial, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
    rw [this]
    exact isPretorsionTheory_top_right hT
  | insert a J _ ih =>
    have : (finInf F (insert a J)).prop = (F a ⊓ finInf F J).prop := by
      funext X
      apply propext
      rw [finInf_prop_iff, inf_prop, Pi.inf_apply, finInf_prop_iff]
      simp only [Finset.mem_insert, forall_eq_or_imp]
      rfl
    rw [this]
    exact isPretorsionTheory_inf (h a) ih
end PretorsionImageClosed.Statement
