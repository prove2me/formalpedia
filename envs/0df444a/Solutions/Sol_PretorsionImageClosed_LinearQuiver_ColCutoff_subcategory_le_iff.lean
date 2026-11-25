-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.ColCutoff.subcategory_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:44.052951+00:00
-- url     : https://prove2.me/submissions/622f5f00-8594-4e94-8cd0-3048e9df6f20

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
namespace ColCutoff
theorem _root_.solution (α α' : ColCutoff n) :
    α'.subcategory (k := k) ≤ α.subcategory ↔ ∀ d, α.α d ≤ α'.α d := by
  constructor
  · intro h d
    by_contra hlt
    have ha : α'.α d < n := by have := α.α_le d; have := d.isLt; omega
    have had : (⟨α'.α d, ha⟩ : Fin n) ≤ d := Fin.le_def.2 (by have := α.α_le d; simp only; omega)
    have := (α.prop_interval_iff had).1 (h _ ((α'.prop_interval_iff had).2 le_rfl))
    simp only at this
    omega
  · intro h X hX
    apply prop_of_forall_retract _ X
    intro a d had hr
    rw [α.prop_interval_iff had]
    exact (h d).trans ((α'.prop_interval_iff had).1 (α'.subcategory.prop_of_retract hr hX))
end ColCutoff
end PretorsionImageClosed.LinearQuiver
