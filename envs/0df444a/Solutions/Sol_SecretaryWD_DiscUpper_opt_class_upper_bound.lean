-- Prove2me | solution 1 for SecretaryWD.DiscUpper.opt_class_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:30:39.592297+00:00
-- url     : https://prove2.me/submissions/6b4cc840-c81d-4679-9a53-630423600f08

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_DiscountedModel

set_option autoImplicit false

open SecretaryWD.DiscUpper in
theorem SDU8ab0be7c_avg_le {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) (B : ℝ)
    (hf : ∀ π, f π ≤ B) : uniformAvg f ≤ B := by
  unfold uniformAvg
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hsum : ∑ π : Equiv.Perm (Fin n), f π ≤ (n.factorial : ℝ) * B := by
    calc ∑ π : Equiv.Perm (Fin n), f π ≤ ∑ _π : Equiv.Perm (Fin n), B :=
          Finset.sum_le_sum fun π _ => hf π
      _ = (n.factorial : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  linarith

open SecretaryWD.DiscUpper in
theorem solution (n : ℕ) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ) (hc : 1 ≤ c) :
    optClass d v c ≤ (2 : ℝ)⁻¹ ^ c * (2 * (n : ℝ) ^ 2 * dmax d * vmax v) := by
  have hdm : 0 ≤ dmax d := Real.iSup_nonneg hd
  have hvm : 0 ≤ vmax v := Real.iSup_nonneg hv
  have hvle : ∀ e, v e ≤ vmax v := fun e => le_ciSup (Finite.bddAbove_range v) e
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  set B : ℝ := (2 : ℝ)⁻¹ ^ c * (2 * dmax d * vmax v) with hB
  have hB0 : 0 ≤ B := by positivity
  have hcard : ((discountClass d c).card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 : (discountClass d c).card ≤ n := by
      calc (discountClass d c).card ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_univ _
        _ = n := by simp
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    calc ((discountClass d c).card : ℝ) ≤ n := by exact_mod_cast h1
      _ ≤ _ := h2
  unfold optClass
  apply SDU8ab0be7c_avg_le
  intro π
  calc _ ≤ ∑ _t ∈ discountClass d c, B := by
        apply Finset.sum_le_sum
        intro t ht
        simp only [discountClass, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        split_ifs
        · have h1 : d t * v (π t) ≤ (2 * dmax d / 2 ^ c) * vmax v :=
            mul_le_mul ht.2 (hvle _) (hv _) (by positivity)
          have h3 : (2 * dmax d / 2 ^ c) * vmax v = B := by
            rw [hB, inv_pow]; field_simp
          linarith
        · exact hB0
    _ = ((discountClass d c).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB0
    _ = (2 : ℝ)⁻¹ ^ c * (2 * (n : ℝ) ^ 2 * dmax d * vmax v) := by rw [hB]; ring
