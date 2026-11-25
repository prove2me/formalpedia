-- Prove2me | solution 1 for SmallRatio.pow_mul_rem_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:37:19.105164+00:00
-- url     : https://prove2.me/submissions/6c46b64c-56d8-4a1a-bb0d-42c5f0ba8154

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_two_rem_lt
attribute [local simp] SmallRatio.rem_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.den_one

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution (i : ℕ) (hi : 2 * i ≤ steps k h) :
    2 ^ i * rem k h (2 * i) ≤ k ∧ (2 * i + 1 ≤ steps k h → 2 ^ i * rem k h (2 * i + 1) ≤ k) := by
  induction i with
  | zero => exact ⟨by simp, fun _ => by simpa using hhk.le⟩
  | succ i ih =>
    have ih := ih (by omega)
    constructor
    · have h1 := two_rem_lt hh hhk hc (show 2 * i + 1 < steps k h by omega)
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_succ]
      nlinarith [ih.1]
    · intro hle
      have h1 := two_rem_lt hh hhk hc (show 2 * i + 1 + 1 < steps k h by omega)
      have h2 := ih.2 (by omega)
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, pow_succ]
      nlinarith
end SmallRatio
