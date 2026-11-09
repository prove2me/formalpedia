-- Prove2me | solution 1 for SeqPostedPricing.PartitionSPM.display_3_correlation_gap
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:22:40.803896+00:00
-- url     : https://prove2.me/submissions/2f5a9fe3-47dd-4356-b211-9042bec1080e

import Mathlib

/-- Display (3): `1 - ∏(1 - qᵢ) ≥ 1 - (1 - s/n)^n ≥ (1 - 1/e)s` for `qᵢ ∈ [0,1]`,
`∑ qᵢ = s ≤ 1`. -/
theorem solution {n : ℕ} (q : Fin n → ℝ) (s : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hs : ∑ i, q i = s) (hs1 : s ≤ 1) :
    1 - (1 - s / n) ^ n ≤ 1 - ∏ i, (1 - q i) ∧
      (1 - Real.exp (-1)) * s ≤ 1 - (1 - s / n) ^ n := by
  have hs_nonneg : 0 ≤ s := by
    rw [← hs]
    exact Finset.sum_nonneg (fun i _ => hq0 i)
  constructor
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      simp
    · have hnR : (0:ℝ) < n := by exact_mod_cast hn
      have hnR' : (n:ℝ) ≠ 0 := ne_of_gt hnR
      have hz : ∀ i : Fin n, 0 ≤ 1 - q i := fun i => by linarith [hq1 i]
      have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ((n:ℝ)⁻¹) := fun _ _ => by positivity
      have hw' : ∑ i ∈ (Finset.univ : Finset (Fin n)), ((n:ℝ)⁻¹) = 1 := by
        simp [Finset.sum_const, hnR']
      have hamgm := Real.geom_mean_le_arith_mean_weighted
        (s := (Finset.univ : Finset (Fin n))) (fun _ => (n:ℝ)⁻¹) (fun i => 1 - q i)
        hw hw' (fun i _ => hz i)
      have hsum1 : ∑ i : Fin n, (1 - q i) = (n:ℝ) - s := by
        rw [Finset.sum_sub_distrib]
        simp [hs]
      have hrhs : ∑ i : Fin n, ((n:ℝ)⁻¹) * (1 - q i) = 1 - s / n := by
        rw [← Finset.mul_sum, hsum1]
        field_simp
      rw [hrhs] at hamgm
      have hlhs : (∏ i : Fin n, (1 - q i) ^ ((n:ℝ)⁻¹)) ^ n = ∏ i : Fin n, (1 - q i) := by
        rw [← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro i _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i)]
        have h1 : ((n:ℝ)⁻¹) * (n:ℝ) = 1 := inv_mul_cancel₀ hnR'
        rw [h1, Real.rpow_one]
      have hprod : ∏ i : Fin n, (1 - q i) ≤ (1 - s / n) ^ n := by
        rw [← hlhs]
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hz i) _)) hamgm n
      linarith
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
      rw [← hs]
      simp
    · have hnR : (0:ℝ) < n := by exact_mod_cast hn
      have hsn : s ≤ (n:ℝ) := le_trans hs1 (by exact_mod_cast hn)
      have hexp : (1 - s / n) ^ n ≤ Real.exp (-s) := Real.one_sub_div_pow_le_exp_neg hsn
      have hconv := convexOn_exp
      have hchord : Real.exp (-s) ≤ 1 - (1 - Real.exp (-1)) * s := by
        have h2 := hconv.2
        have h := h2 (x := (0:ℝ)) (Set.mem_univ _) (y := (-1:ℝ)) (Set.mem_univ _)
          (a := 1 - s) (b := s) (by linarith [hs1]) (by linarith [hs_nonneg]) (by ring)
        have h' : Real.exp ((1 - s) * 0 + s * (-1)) ≤
            (1 - s) * Real.exp 0 + s * Real.exp (-1) := by
          simpa [smul_eq_mul] using h
        have harg : (1 - s) * 0 + s * (-1) = -s := by ring
        rw [harg, Real.exp_zero] at h'
        nlinarith [h']
      nlinarith [hexp, hchord]
