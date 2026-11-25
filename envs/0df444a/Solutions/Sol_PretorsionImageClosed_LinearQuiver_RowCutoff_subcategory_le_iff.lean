-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.RowCutoff.subcategory_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:41.339708+00:00
-- url     : https://prove2.me/submissions/66ab034e-bc04-408d-bc99-23c4a93d2eec

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Cutoffs
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
attribute [local instance] Classical.propDecidable
namespace PretorsionImageClosed.LinearQuiver
namespace RowCutoff
theorem _root_.solution (β β' : RowCutoff n) :
    β.subcategory (k := k) ≤ β'.subcategory ↔ ∀ a, β.β a ≤ β'.β a := by
  constructor
  · intro h a
    by_contra hlt
    have hd : β'.β a < n := (not_le.1 hlt).trans_le (β.β_le a)
    have had : a ≤ (⟨β'.β a, hd⟩ : Fin n) := Fin.le_def.2 (β'.le_β a)
    have := (β'.prop_interval_iff had).1 (h _ ((β.prop_interval_iff had).2 (not_le.1 hlt)))
    exact lt_irrefl _ this
  · intro h X hX
    apply prop_of_forall_retract _ X
    intro a d had hr
    rw [β'.prop_interval_iff had]
    exact lt_of_lt_of_le ((β.prop_interval_iff had).1 (β.subcategory.prop_of_retract hr hX)) (h a)
end RowCutoff
end PretorsionImageClosed.LinearQuiver
