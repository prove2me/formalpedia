-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.indCard_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:20:59.842558+00:00
-- url     : https://prove2.me/submissions/6a8e11e7-7f2f-47f3-8668-d013ed97fd8e

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_eq


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (β : RowCutoff n) (α : ColCutoff n) :
    indCard ((β.subcategory (k := k)).prop ⊓ α.subcategory.prop) = middleCount β α := by
  have h := indCard_eq (β.subcategory (k := k) ⊓ α.subcategory)
  rw [Subcategory.inf_prop] at h
  rw [h, Nat.subtype_card (univ.filter (fun p : Fin n × Fin n =>
    p.1 ≤ p.2 ∧ p.2.val < β.β p.1 ∧ α.α p.2 ≤ p.1.val)) ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    unfold middleCount colCount
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.card_filter]
  · intro p
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨h1, (β.prop_interval_iff h1).2 h2, (α.prop_interval_iff h1).2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨Finset.mem_univ _, h1, (β.prop_interval_iff h1).1 h2, (α.prop_interval_iff h1).1 h3⟩
end PretorsionImageClosed.LinearQuiver
