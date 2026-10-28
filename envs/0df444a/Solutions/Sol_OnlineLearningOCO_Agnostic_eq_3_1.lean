-- Prove2me | solution 1 for OnlineLearningOCO.Agnostic.eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:29:23.424953+00:00
-- url     : https://prove2.me/submissions/ca945954-af05-494a-9528-5f565aef96dc

import Mathlib

theorem solution (T L : ℕ) (hL : 1 ≤ L) (hLT : L ≤ T) :
    ((Finset.range T).powerset.filter (fun I ↦ I.card ≤ L)).card =
        ∑ j ∈ Finset.range (L + 1), T.choose j ∧
      (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) ≤ (Real.exp 1 * T / L) ^ L := by
  constructor
  · have : (Finset.range T).powerset.filter (fun I ↦ I.card ≤ L) =
        (Finset.range (L + 1)).biUnion (fun j => (Finset.range T).powersetCard j) := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨I.card, by omega, h1, rfl⟩
      · rintro ⟨j, hj, h1, rfl⟩; exact ⟨h1, by omega⟩
    rw [this, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.card_powersetCard, Finset.card_range]
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro I hi hj
      rw [Finset.mem_powersetCard] at hi hj
      exact hij (hi.2.symm.trans hj.2)
  · have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le hL hLT)
    set x : ℝ := (L : ℝ) / T with hx
    have hx0 : 0 < x := div_pos hLpos hTpos
    have hx1 : x ≤ 1 := by rw [hx, div_le_one hTpos]; exact_mod_cast hLT
    -- Σ_{j ≤ L} C(T,j) x^L ≤ Σ_{j ≤ L} C(T,j) x^j ≤ (1+x)^T ≤ exp(x T) = exp L
    have h1 : (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) * x ^ L ≤
        ∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ) * x ^ j := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one hx0.le hx1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    have h2 : ∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ) * x ^ j ≤ (x + 1) ^ T := by
      rw [add_pow]
      have hsub : Finset.range (L + 1) ⊆ Finset.range (T + 1) := by
        intro j hj; simp only [Finset.mem_range] at *; omega
      calc ∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ) * x ^ j
          = ∑ j ∈ Finset.range (L + 1), x ^ j * 1 ^ (T - j) * (T.choose j : ℝ) := by
            apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ ∑ j ∈ Finset.range (T + 1), x ^ j * 1 ^ (T - j) * (T.choose j : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    have h3 : (x + 1) ^ T ≤ Real.exp L := by
      have := Real.add_one_le_exp x
      calc (x + 1) ^ T ≤ (Real.exp x) ^ T :=
            pow_le_pow_left₀ (by linarith) (by linarith) T
        _ = Real.exp (x * T) := by rw [← Real.exp_nat_mul]; ring_nf
        _ = Real.exp L := by rw [hx, div_mul_cancel₀ _ hTpos.ne']
    have hxL : 0 < x ^ L := pow_pos hx0 L
    have key : (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) ≤ Real.exp L / x ^ L := by
      rw [le_div_iff₀ hxL]; linarith
    calc (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) ≤ Real.exp L / x ^ L := key
      _ = (Real.exp 1 * T / L) ^ L := by
        rw [hx, div_pow, div_div_eq_mul_div, mul_div_assoc, ← Real.exp_one_pow, div_pow, mul_pow]
        field_simp
