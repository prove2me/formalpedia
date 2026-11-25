-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_not_mem_tgt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:22:02.842275+00:00
-- url     : https://prove2.me/submissions/8c02a92d-63d4-4f3b-b62f-10bc106d9de6

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
variable {k}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    {i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ b)) : coord η i = 0 :=
  coe_eq_zero_of_not_mem k h _
end PretorsionImageClosed.LinearQuiver
