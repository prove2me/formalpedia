-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.unit_val_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:23:59.542025+00:00
-- url     : https://prove2.me/submissions/e00e7f04-91a3-41f2-b426-66803ed5343e

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c d i : Fin n} (h : c ≤ i ∧ i ≤ d) : (unit k c d i : k) = 1 := by
  rw [unit_val, if_pos h]
end PretorsionImageClosed.LinearQuiver
