-- Prove2me | solution 1 for actuarial_e_age_mixture_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:12:42.752274+00:00
-- url     : https://prove2.me/submissions/61dd2c42-5727-41c0-b8ba-15a2021ff061

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_ageMixtureLaw
import Definitions.Def_actuarial_e_spousePayment
import Definitions.Def_actuarial_e_overlapPayment
import Definitions.Def_actuarial_e_expect

open ActuarialDeathE

open ActuarialDeathE in
theorem ap_expect_add (h : ℕ) (p f g : ℕ → ℕ → ℝ) :
    expect h p (fun i j => f i j + g i j) = expect h p f + expect h p g := by
  unfold expect ActuarialJointD.expect
  simp only [mul_add, Finset.sum_add_distrib]

open ActuarialDeathE in
theorem ap_expect_sum (h n : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) (f : ℕ → ℕ → ℕ → ℝ) :
    expect h p (fun i j => ∑ t ∈ Finset.range n, d t * f i j t)
      = ∑ t ∈ Finset.range n, d t * expect h p (fun i j => f i j t) := by
  unfold expect ActuarialJointD.expect
  simp_rw [Finset.mul_sum]
  calc _ = ∑ i ∈ Finset.range (h+1), ∑ t ∈ Finset.range n, ∑ j ∈ Finset.range (h+1),
        p i j * (d t * f i j t) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring

open ActuarialDeathE in
theorem ap_expect_mix (h a : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    expect h (ageMixtureLaw h a w laws) f = ∑ k ∈ Finset.range a, w k * expect h (laws k) f := by
  unfold expect ActuarialJointD.expect ageMixtureLaw
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ i ∈ Finset.range (h+1), ∑ k ∈ Finset.range a, ∑ j ∈ Finset.range (h+1),
        w k * laws k i j * f i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring

open ActuarialDeathE in
theorem ap_spouse_split (h e r g i j t : ℕ) (a b c inc : ℕ → ℝ) :
    spousePayment h e r g i j t a b c inc false
      = spousePayment h e r g i j t a b c inc true + overlapPayment h r g i j t c inc := by
  unfold spousePayment overlapPayment
  by_cases ht : t < r + g <;> simp [ht] <;> ring

theorem solution (h : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ageMixtureLaw h 0 w laws i j = 0 := by
  simp [ageMixtureLaw]

