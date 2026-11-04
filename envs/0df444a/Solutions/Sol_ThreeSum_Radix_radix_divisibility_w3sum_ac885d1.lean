-- Prove2me | solution 1 for ThreeSum.Radix.radix_divisibility_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:28.781195+00:00
-- url     : https://prove2.me/submissions/fba7d741-039f-42d1-b2f3-7a2048615a65

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Radix

set_option autoImplicit false
open ThreeSum ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
namespace ThreeSum.Radix
theorem _root_.solution (p a h t : ℤ) (hp : p ≠ 0) (j : ℕ) :
    p ^ (j + 1) ∣ a - (h + p * t) ↔
      p ∣ a - h ∧ p ^ j ∣ (a - h) / p - t := by
  constructor
  · intro hd
    have hd₁ : p ∣ a - h := by
      have hpow : p ∣ p ^ (j + 1) := dvd_pow_self _ (by omega)
      have hm : p ∣ p * t := dvd_mul_right _ _
      have hs := Int.dvd_add (dvd_trans hpow hd) hm
      convert hs using 1 <;> ring
    refine ⟨hd₁, ?_⟩
    have heq := Int.mul_ediv_cancel' hd₁
    have hrew : a - (h + p * t) = p * ((a - h) / p - t) := by
      nlinarith
    rw [hrew, pow_succ', mul_dvd_mul_iff_left hp] at hd
    exact hd
  · rintro ⟨hd₁, hd₂⟩
    have heq := Int.mul_ediv_cancel' hd₁
    have hrew : a - (h + p * t) = p * ((a - h) / p - t) := by
      nlinarith
    rw [hrew, pow_succ', mul_dvd_mul_iff_left hp]
    exact hd₂
end ThreeSum.Radix
