-- Prove2me | solution 1 for OncePaid.Sparse.factorial_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:29:18.211587+00:00
-- url     : https://prove2.me/submissions/9d472605-1e19-4a47-994a-717860bf08a4

import Mathlib

theorem factorial_estimate_aux :
    ∀ r ∈ Finset.Icc 1 102,
      Nat.factorial r * 27182818286 ^ r ≤ (r + 6) ^ r * 10 ^ (10 * r) := by
  decide +kernel

/-- App. A.3, factorial estimate, p. 36: `(r!)^{1/r} ≤ (r + 6)/e` for all integers
`1 ≤ r ≤ 102`, and `6/e > 1`. -/
theorem solution :
    (∀ r : ℕ, 1 ≤ r → r ≤ 102 →
      ((Nat.factorial r : ℕ) : ℝ) ^ ((1 : ℝ) / (r : ℝ)) ≤ ((r : ℝ) + 6) / Real.exp 1) ∧
    1 < 6 / Real.exp 1 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  constructor
  · intro r h1 h2
    have hr : (r : ℝ) ≠ 0 := by positivity
    have hn := factorial_estimate_aux r (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have hR : ((Nat.factorial r : ℕ) : ℝ) * (27182818286 : ℝ) ^ r ≤
        ((r : ℝ) + 6) ^ r * 10 ^ (10 * r) := by exact_mod_cast hn
    have hpow : (Real.exp 1) ^ r ≤ ((27182818286 : ℝ) / 10 ^ 10) ^ r := by
      apply pow_le_pow_left₀ hepos.le
      norm_num at he ⊢; linarith
    have hfac : ((Nat.factorial r : ℕ) : ℝ) ≤ (((r : ℝ) + 6) / Real.exp 1) ^ r := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      calc ((Nat.factorial r : ℕ) : ℝ) * (Real.exp 1) ^ r
          ≤ ((Nat.factorial r : ℕ) : ℝ) * ((27182818286 : ℝ) / 10 ^ 10) ^ r := by gcongr
        _ = ((Nat.factorial r : ℕ) : ℝ) * (27182818286 : ℝ) ^ r / 10 ^ (10 * r) := by
            rw [div_pow, ← pow_mul]; ring
        _ ≤ ((r : ℝ) + 6) ^ r := by
            rw [div_le_iff₀ (by positivity)]; exact hR
    calc ((Nat.factorial r : ℕ) : ℝ) ^ ((1 : ℝ) / (r : ℝ))
        ≤ ((((r : ℝ) + 6) / Real.exp 1) ^ r) ^ ((1 : ℝ) / (r : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity) hfac (by positivity)
      _ = ((r : ℝ) + 6) / Real.exp 1 := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  · rw [lt_div_iff₀ hepos]
    norm_num at he ⊢; linarith
