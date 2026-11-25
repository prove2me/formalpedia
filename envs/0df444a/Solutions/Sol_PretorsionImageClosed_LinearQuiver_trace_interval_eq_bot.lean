-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.trace_interval_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:37:53.937865+00:00
-- url     : https://prove2.me/submissions/bd5da39d-241d-4fa1-aa3b-becbdaa12fd6

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_interval_of_prop_suffix


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
variable {T F : Subcategory (Statement.LinRep k n)}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c d : Fin n}
    (h : ∀ i, c ≤ i → i ≤ d → ¬ T.prop (interval k i d)) : T.trace (interval k c d) = ⊥ := by
  rcases eq_bot_or_eq_suffix (T.trace (interval k c d)) with h0 | ⟨u', hcu', hu'd, hK⟩
  · exact h0
  · exact absurd (prop_interval_of_prop_suffix T hcu' (by rw [← hK]; exact T.prop_trace _))
      (h u' hcu' hu'd)
end PretorsionImageClosed.LinearQuiver
