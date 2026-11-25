-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.trace_interval_eq_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:38:04.935318+00:00
-- url     : https://prove2.me/submissions/2d072f49-431f-4ee3-a5eb-b71a5d5b33cb

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_interval_of_prop_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_suffix
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_le


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
theorem _root_.solution (hT : T.IsQuotientClosed) {c u d : Fin n} (hcu : c ≤ u)
    (hu : T.prop (interval k u d)) (hmin : ∀ i, c ≤ i → i < u → ¬ T.prop (interval k i d)) :
    T.trace (interval k c d) = suffix c d u hcu := by
  apply le_antisymm
  · rcases eq_bot_or_eq_suffix (T.trace (interval k c d)) with h0 | ⟨u', hcu', -, hK⟩
    · rw [h0]
      exact bot_le
    · have hu' : T.prop (interval k u' d) :=
        prop_interval_of_prop_suffix T hcu' (by rw [← hK]; exact T.prop_trace _)
      rw [hK]
      rcases le_or_gt u u' with huu' | hu'u
      · exact suffix_le_suffix hcu huu'
      · exact absurd hu' (hmin u' hcu' hu'u)
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm hu)
end PretorsionImageClosed.LinearQuiver
