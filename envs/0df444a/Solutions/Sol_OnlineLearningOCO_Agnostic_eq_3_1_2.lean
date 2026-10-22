-- Prove2me | solution 2 for OnlineLearningOCO.Agnostic.eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:00:05.702897+00:00
-- url     : https://prove2.me/submissions/086b286c-48f0-4fcb-a8b8-d9db8dd2b15b

import Mathlib
set_option autoImplicit false

theorem solution (T L : ℕ) (hL : 1 ≤ L) (hLT : L ≤ T) :
    ((Finset.range T).powerset.filter (fun I ↦ I.card ≤ L)).card =
        ∑ j ∈ Finset.range (L + 1), T.choose j ∧
      (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) ≤ (Real.exp 1 * T / L) ^ L := by
  constructor
  · rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (L + 1))]
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ L := by simpa [Nat.lt_succ_iff] using hj
      have : (((Finset.range T).powerset.filter (fun I ↦ I.card ≤ L)).filter (fun I => I.card = j))
          = Finset.powersetCard j (Finset.range T) := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
      rw [this, Finset.card_powersetCard, Finset.card_range]
    · intro I hI
      simp at hI ⊢
      omega
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le hL hLT)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    set x : ℝ := (L : ℝ) / T with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 := by
      rw [hx, div_le_one hTpos]; exact_mod_cast hLT
    have h1 : (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) * x ^ L ≤ (1 + x) ^ T := by
      calc (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) * x ^ L
          = ∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ) * x ^ L := by rw [Finset.sum_mul]
        _ ≤ ∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ) * x ^ j := by
            apply Finset.sum_le_sum
            intro j hj
            have hj' : j ≤ L := by simpa [Nat.lt_succ_iff] using hj
            exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 hj') (Nat.cast_nonneg _)
        _ ≤ ∑ j ∈ Finset.range (T + 1), (T.choose j : ℝ) * x ^ j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_subset_range.mpr (by omega)
            · intro j _ _; positivity
        _ = (1 + x) ^ T := by
            rw [add_comm 1 x, add_pow]
            apply Finset.sum_congr rfl
            intro j _
            simp [mul_comm]
    have h2 : (1 + x) ^ T ≤ Real.exp L := by
      calc (1 + x) ^ T ≤ (Real.exp x) ^ T := by
            apply pow_le_pow_left₀ (by positivity)
            linarith [Real.add_one_le_exp x]
        _ = Real.exp L := by
            rw [← Real.exp_nat_mul]
            congr 1
            rw [hx]; field_simp
    have hxL : 0 < x ^ L := by positivity
    have h3 : (Real.exp 1 * T / L) ^ L = Real.exp L / x ^ L := by
      rw [hx, div_pow, div_pow, mul_pow, ← Real.exp_nat_mul]
      field_simp
    rw [h3, le_div_iff₀ hxL]
    exact h1.trans h2
