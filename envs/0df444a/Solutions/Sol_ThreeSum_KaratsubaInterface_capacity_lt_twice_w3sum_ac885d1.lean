-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.capacity_lt_twice_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:19.728613+00:00
-- url     : https://prove2.me/submissions/c0c1a0e2-ea3e-4dec-a782-4bdc3292137e

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface

set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution {p : ℕ} (hp : 0 < p) : capacity p < 2 * p := by
  by_cases h1 : p = 1
  · subst p
    norm_num [capacity]
  have hp1 : 1 < p := by omega
  have hk : 0 < Nat.clog 2 p := Nat.clog_pos (by decide) hp1
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hp1
  rw [Nat.pred_eq_sub_one] at hpred
  calc
    capacity p = 2 * 2 ^ (Nat.clog 2 p - 1) := by
      unfold capacity
      conv_lhs =>
        rw [show Nat.clog 2 p = (Nat.clog 2 p - 1) + 1 by omega, pow_succ]
      rw [Nat.mul_comm]
    _ < 2 * p := Nat.mul_lt_mul_of_pos_left hpred (by decide)
end ThreeSum.KaratsubaInterface
