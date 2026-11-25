-- Prove2me | solution 1 for PretorsionImageClosed.Statement.exists_reject_finInf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:27.199875+00:00
-- url     : https://prove2.me/submissions/bd69e9d9-ea1e-4353-a4f1-288ff4e96675

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_finInf_prop_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_isSubobjectClosed_finInf
public import Theorems.Thm_PretorsionImageClosed_Statement_isSubobjectClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le
public import Theorems.Thm_PretorsionImageClosed_Subobject_exists_maximal_of_nonempty


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
omit hT
namespace PretorsionImageClosed.Statement
theorem _root_.solution (X : C) :
    ∃ J₀ : Finset ι, ∀ J : Finset ι, J₀ ⊆ J →
      (finInf F J).reject X = (Subcategory.iInf F).reject X := by
  classical
  have hle : ∀ J : Finset ι, (finInf F J).reject X ≤ (Subcategory.iInf F).reject X := by
    intro J
    rw [le_reject_iff (isSubobjectClosed_iInf h)]
    intro Y g hY
    exact reject_arrow_comp_eq_zero (isSubobjectClosed_finInf h J) g
      ((finInf_prop_iff F J Y).2 fun i _ => (iInf_prop_iff F Y).1 hY i)
  have hmono : ∀ J J' : Finset ι, J ⊆ J' → (finInf F J).reject X ≤ (finInf F J').reject X := by
    intro J J' hJJ'
    rw [le_reject_iff (isSubobjectClosed_finInf h J')]
    intro Y g hY
    exact reject_arrow_comp_eq_zero (isSubobjectClosed_finInf h J) g
      ((finInf_prop_iff F J Y).2 fun i hi => (finInf_prop_iff F J' Y).1 hY i (hJJ' hi))
  obtain ⟨S, ⟨J₀, rfl⟩, hmax⟩ := Subobject.exists_maximal_of_nonempty
    (Set.range fun J : Finset ι => (finInf F J).reject X) ⟨_, ⟨∅, rfl⟩⟩
  have heq : (finInf F J₀).reject X = (Subcategory.iInf F).reject X := by
    apply le_antisymm (hle J₀)
    apply reject_le (isSubobjectClosed_iInf h)
    rw [iInf_prop_iff]
    intro i
    have hi : (finInf F J₀).reject X = (finInf F (insert i J₀)).reject X :=
      hmax _ ⟨insert i J₀, rfl⟩ (hmono _ _ (Finset.subset_insert _ _))
    rw [hi]
    exact (finInf_prop_iff F _ _).1 ((finInf F _).prop_cokernel_reject X) i (Finset.mem_insert_self _ _)
  refine ⟨J₀, fun J hJ => le_antisymm (hle J) ?_⟩
  rw [← heq]
  exact hmono _ _ hJ
end PretorsionImageClosed.Statement
