-- Prove2me | solution 1 for SmallRatio.two_le_rem_of_lt_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:19:36.295214+00:00
-- url     : https://prove2.me/submissions/a12aca9e-d30a-4e03-8211-bea1ad4c6464

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
omit hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j < steps k h) : 2 ≤ rem k h j := by
  have := Nat.find_min (⟨k + 1, Or.inr rfl⟩ : ∃ j, rem k h j ≤ 1 ∨ j = k + 1) hj
  push Not at this
  omega
end SmallRatio
