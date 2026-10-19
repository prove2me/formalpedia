-- Prove2me | solution 1 for RamanujanNotebooks.entry_15_12_i
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:32:46.491919+00:00
-- url     : https://prove2.me/submissions/cccacb45-050f-48e7-b2ce-941be8819076

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_eisQ
import Definitions.Def_RamanujanNotebooks_shared_eisR
import Definitions.Def_RamanujanNotebooks_shared_eulerF
import Definitions.Def_RamanujanNotebooks_shared_qPochInf

namespace RNE15
open RamanujanNotebooks Complex UpperHalfPlane ModularForm EisensteinSeries ArithmeticFunction

lemma lambert (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    (∑' m : ℕ, ((m : ℂ) + 1) ^ k * q ^ (m + 1) / (1 - q ^ (m + 1))) =
      ∑' n : ℕ+, (ArithmeticFunction.sigma k n : ℂ) * q ^ (n : ℕ) := by
  rw [← tsum_pow_div_one_sub_eq_tsum_sigma hq k,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ k * q ^ n / (1 - q ^ n))]
  push_cast; rfl

lemma E4_eq (τ : ℍ) : E₄ τ = eisQ (cexp (2 * Real.pi * Complex.I * τ)) := by
  rw [eisQ, lambert _ (UpperHalfPlane.norm_exp_two_pi_I_lt_one τ) 3]
  rw [q_expansion_bernoulli (by norm_num) ⟨2, rfl⟩ τ, show bernoulli 4 = -1 / 30 by decide +kernel]
  simp only [zpow_natCast]
  push_cast
  ring

lemma E6_eq (τ : ℍ) : E₆ τ = eisR (cexp (2 * Real.pi * Complex.I * τ)) := by
  rw [eisR, lambert _ (UpperHalfPlane.norm_exp_two_pi_I_lt_one τ) 5]
  rw [q_expansion_bernoulli (by norm_num) ⟨3, rfl⟩ τ, show bernoulli 6 = 1 / 42 by decide +kernel]
  simp only [zpow_natCast]
  push_cast
  ring

theorem main (q : ℂ) (hq : ‖q‖ < 1) :
    eisQ q ^ 3 - eisR q ^ 2 = 1728 * (q * eulerF q ^ 24) := by
  by_cases hq0 : q = 0
  · subst hq0
    simp [eisQ, eisR]
  have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0
  set τ : ℍ := ⟨Function.Periodic.invQParam 1 q, him⟩
  have hqτ : cexp (2 * Real.pi * Complex.I * τ) = q := by
    have := Function.Periodic.qParam_right_inv (h := 1) one_ne_zero hq0
    rw [Function.Periodic.qParam] at this
    simpa using this
  have hD := discriminant_eq_q_prod τ
  have hD2 := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [← hqτ, ← E4_eq, ← E6_eq]
  have hprod : (∏' n : ℕ, (1 - eta_q n τ) ^ 24) = eulerF (cexp (2 * Real.pi * Complex.I * τ)) ^ 24 := by
    rw [eulerF, qPochInf, hqτ]
    simp_rw [ModularForm.eta_q_eq_pow, hqτ]
    rw [(ModularForm.multipliable_one_sub_pow hq).tprod_pow]
    congr 2; ext k; ring
  have h𝕢 : Function.Periodic.qParam 1 (τ : ℂ) = cexp (2 * Real.pi * Complex.I * τ) := by simp [Function.Periodic.qParam]
  rw [hprod, h𝕢] at hD
  rw [← hD]
  linear_combination (-1728 : ℂ) * hD2

end RNE15

open RamanujanNotebooks in
theorem solution (q : ℂ) (hq : ‖q‖ < 1) :
    eisQ q ^ 3 - eisR q ^ 2 = 1728 * (q * eulerF q ^ 24) :=
  RNE15.main q hq
