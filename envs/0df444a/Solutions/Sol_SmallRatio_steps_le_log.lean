-- Prove2me | solution 1 for SmallRatio.steps_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:42.132815+00:00
-- url     : https://prove2.me/submissions/d13f9d4e-4342-4edd-9d21-68daaac2f1f3

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_steps
public import Theorems.Thm_SmallRatio_pow_mul_rem_le

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution : steps k h ≤ 2 * Nat.log 2 k + 1 := by
  have hr := rem_steps hh hhk hc
  obtain ⟨i, hi⟩ : ∃ i, steps k h = 2 * i ∨ steps k h = 2 * i + 1 :=
    ⟨steps k h / 2, by omega⟩
  have hpow : 2 ^ i ≤ k := by
    rcases hi with hi | hi
    · have := (pow_mul_rem_le hh hhk hc i (by omega)).1
      rw [← hi, hr, mul_one] at this; exact this
    · have := (pow_mul_rem_le hh hhk hc i (by omega)).2 (by omega)
      rw [← hi, hr, mul_one] at this; exact this
  have := Nat.le_log_of_pow_le (by norm_num) hpow
  omega
end SmallRatio
