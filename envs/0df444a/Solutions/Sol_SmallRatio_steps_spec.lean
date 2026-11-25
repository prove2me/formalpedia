-- Prove2me | solution 1 for SmallRatio.steps_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:37.232448+00:00
-- url     : https://prove2.me/submissions/21063a7c-128f-4e5e-9c88-7afea6c5f2de

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_exists_rem_le_one

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
omit hh hc
namespace SmallRatio
theorem _root_.solution : rem k h (steps k h) ≤ 1 := by
  obtain ⟨j, hj, hj1⟩ := exists_rem_le_one (k := k) (h := h)
  have hle : steps k h ≤ j := Nat.find_min' _ (Or.inl hj1)
  rcases Nat.find_spec (⟨k + 1, Or.inr rfl⟩ : ∃ j, rem k h j ≤ 1 ∨ j = k + 1) with h1 | h1
  · exact h1
  · exfalso; unfold steps at hle; omega
end SmallRatio
