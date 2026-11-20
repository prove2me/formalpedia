-- Prove2me | solution 1 for Sensitivity.BoolFun.sensitiveAt_of_paritySigned_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:24.682089+00:00
-- url     : https://prove2.me/submissions/7ec329e5-7879-4c2e-9f79-f01457017c80

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
import Theorems.Thm_Sensitivity_parity_ne_zero
import Theorems.Thm_Sensitivity_parity_flipBit

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n)
    (x : Fin n → Bool) (i : Fin n)
    (h : f.paritySigned (flipBit x i) = f.paritySigned x) :
    f.sensitiveAt x i := by
  unfold sensitiveAt
  unfold paritySigned pmOne at h
  rw [parity_flipBit] at h
  -- h : (if f (flipBit x i) then 1 else -1) * -parity x =
  --     (if f x then 1 else -1) * parity x
  intro heq
  rw [heq] at h
  have hpnz := parity_ne_zero x
  -- Now h says: (if f x then 1 else -1) * -parity x = (if f x then 1 else -1) * parity x
  -- So (if f x then 1 else -1) * (-parity x - parity x) = 0
  have : (if f x then (1 : ℤ) else -1) * (-parity x - parity x) = 0 := by linarith
  rw [show -parity x - parity x = -2 * parity x from by ring] at this
  have := mul_eq_zero.mp this
  rcases this with h1 | h1
  · split_ifs at h1; all_goals omega
  · exact hpnz (by linarith)
end BoolFun
end Sensitivity
