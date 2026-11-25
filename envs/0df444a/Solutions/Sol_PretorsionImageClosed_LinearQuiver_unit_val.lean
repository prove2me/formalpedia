-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.unit_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:20:32.657152+00:00
-- url     : https://prove2.me/submissions/b537fd89-5531-45a7-8694-391de89b4fe5

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom

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
theorem _root_.solution (c d i : Fin n) : (unit k c d i : k) = if c ≤ i ∧ i ≤ d then 1 else 0 := rfl
end PretorsionImageClosed.LinearQuiver
