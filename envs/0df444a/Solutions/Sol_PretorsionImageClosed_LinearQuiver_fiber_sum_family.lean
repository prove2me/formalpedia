-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.fiber_sum_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:41:28.374962+00:00
-- url     : https://prove2.me/submissions/6952ecb9-f551-40f4-9e4c-2193116b5fe8

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_restrict_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_glue_JOf
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_JOf_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_ClosedFamily_restrict_glue
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_ClosedFamily_glue_JOf

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (D : ClosedFamily n) (f : ClosedFamily (n + 1) → Rq[X])
    (g : Finset (Fin (n + 1)) → Rq[X]) (hfg : ∀ J (hJ : J ⊆ adm D.1), f (D.glue J hJ) = g J) :
    ∑ D' ∈ univ.filter (fun D' : ClosedFamily (n + 1) => D'.restrict = D), f D' =
      ∑ J ∈ (adm D.1).powerset, g J := by
  refine Finset.sum_bij' (fun D' _ => JOf D'.1) (fun J hJ => D.glue J (Finset.mem_powerset.1 hJ))
    ?_ ?_ ?_ ?_ ?_
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    rw [Finset.mem_powerset]
    have := JOf_subset_adm D'.2
    rwa [show D'.1.restrict = D.1 from congrArg Subtype.val hD'.2] at this
  · intro J hJ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, D.restrict_glue J _⟩
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    have key : ∀ (E : ClosedFamily n) (_ : D'.restrict = E) (hJ : JOf D'.1 ⊆ adm E.1),
        E.glue (JOf D'.1) hJ = D' := by
      rintro _ rfl hJ
      exact D'.glue_JOf
    exact key D hD'.2 _
  · intro J hJ
    exact IntervalFamily.JOf_glue D.1 J
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    have hJ' : JOf D'.1 ⊆ adm D.1 := by
      have := JOf_subset_adm D'.2
      rwa [show D'.1.restrict = D.1 from congrArg Subtype.val hD'.2] at this
    have key : ∀ (E : ClosedFamily n) (_ : D'.restrict = E) (hJ : JOf D'.1 ⊆ adm E.1),
        E.glue (JOf D'.1) hJ = D' := by
      rintro _ rfl hJ
      exact D'.glue_JOf
    rw [← hfg _ hJ', key D hD'.2 hJ']
end PretorsionImageClosed.LinearQuiver
