-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_smul_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:17.900471+00:00
-- url     : https://prove2.me/submissions/f9a29fca-62ed-44c3-bf9e-546736f65fb4

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
theorem _root_.solution {c d i : Fin n} (x : intervalSpace k c d i) : x = (x : k) • unit k c d i := by
  apply Subtype.ext
  rw [Submodule.coe_smul, unit_val, smul_eq_mul]
  by_cases h : c ≤ i ∧ i ≤ d
  · rw [if_pos h, mul_one]
  · rw [if_neg h, mul_zero, coe_eq_zero_of_not_mem k h]
end PretorsionImageClosed.LinearQuiver
