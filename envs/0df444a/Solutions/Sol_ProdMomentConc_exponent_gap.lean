-- Prove2me | solution 1 for ProdMomentConc.exponent_gap
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:00:14.817072+00:00
-- url     : https://prove2.me/submissions/7dba8d6b-ecdd-4dad-af7d-128534b9ee4e

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL

theorem solution (α p d₀ d : ℝ) (hp : 0 < p) (hpα : p < α) (hα1 : α < 1)
    (hd₀ : 0 < d₀) (hd₀d : d₀ ≤ d) :
    let z : ℝ := α * (1 - p) / (p * (1 - α))
    let lam0 : ℝ := (1 / d₀) * Real.log z
    let F : ℝ → ℝ → ℝ := fun c s => s * α - (1 / c) * Real.log (1 - p + p * Real.exp (s * c))
    F d₀ lam0 = (1 / d₀) * LimitedPriceChanges.LowerBound.klBer α p ∧
    F d₀ lam0 - F d lam0 =
      (1 / d) * Real.log (1 - p + p * z ^ (d / d₀)) - (1 / d₀) * Real.log (1 - p + p * z) ∧
    1 - p + p * z ^ (d / d₀) ≤ z ^ (d / d₀ - 1) * (1 - p + p * z) ∧
    F d₀ lam0 - F d lam0 ≤ (1 / d₀ - 1 / d) * (Real.log z - Real.log (1 - p + p * z)) ∧
    (1 / d₀ - 1 / d) * (Real.log z - Real.log (1 - p + p * z)) =
      (1 / d₀ - 1 / d) * Real.log (α / p) := by
  dsimp only
  set z : ℝ := α * (1 - p) / (p * (1 - α)) with hz_def
  set lam0 : ℝ := (1 / d₀) * Real.log z with hlam0_def
  set B : ℝ := 1 - p + p * z with hB_def

  have hp1 : p < 1 := lt_trans hpα hα1
  have hα : 0 < α := lt_trans hp hpα
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have h1α : 0 < 1 - α := sub_pos.mpr hα1
  have hd : 0 < d := lt_of_lt_of_le hd₀ hd₀d

  have hz_pos : 0 < z := by
    rw [hz_def]
    exact div_pos (mul_pos hα h1p) (mul_pos hp h1α)

  have hz1 : 1 ≤ z := by
    rw [hz_def]
    apply (le_div_iff₀ (mul_pos hp h1α)).2
    nlinarith [hpα]

  have hB_eq : B = (1 - p) / (1 - α) := by
    rw [hB_def, hz_def]
    field_simp [ne_of_gt hp, ne_of_gt h1α] <;> ring

  have hB_pos : 0 < B := by
    rw [hB_eq]
    exact div_pos h1p h1α

  have hB_ne : B ≠ 0 := ne_of_gt hB_pos

  have hzB : z / B = α / p := by
    rw [hB_eq, hz_def]
    field_simp [ne_of_gt hp, ne_of_gt h1p, ne_of_gt h1α] <;> ring

  have hz_mul : z = (α / p) * B :=
    (div_eq_iff hB_ne).mp hzB

  have hαp_pos : 0 < α / p := div_pos hα hp

  have hlog_z : Real.log z = Real.log (α / p) + Real.log B := by
    rw [hz_mul, Real.log_mul (ne_of_gt hαp_pos) hB_ne]

  have hrecip : (1 - α) / (1 - p) = B⁻¹ := by
    rw [hB_eq]
    field_simp [ne_of_gt h1p, ne_of_gt h1α] <;> ring

  have hlog_recip : Real.log ((1 - α) / (1 - p)) = -Real.log B := by
    rw [hrecip, Real.log_inv]

  have hlam0d₀ : lam0 * d₀ = Real.log z := by
    rw [hlam0_def]
    field_simp [ne_of_gt hd₀] <;> ring

  have hexp0 : Real.exp (lam0 * d₀) = z := by
    rw [hlam0d₀, Real.exp_log hz_pos]

  have hexpd : Real.exp (lam0 * d) = z ^ (d / d₀) := by
    rw [Real.rpow_def_of_pos hz_pos]
    congr 1
    rw [hlam0_def]
    field_simp [ne_of_gt hd₀] <;> ring

  have ht : 1 ≤ d / d₀ := by
    apply (le_div_iff₀ hd₀).2
    simpa using hd₀d

  have hpow1 : 1 ≤ z ^ (d / d₀ - 1) :=
    Real.one_le_rpow hz1 (sub_nonneg.mpr ht)

  have hzpow : z ^ (d / d₀) = z ^ (d / d₀ - 1) * z := by
    have h := Real.rpow_add hz_pos (d / d₀ - 1) 1
    rw [show d / d₀ - 1 + 1 = d / d₀ by ring, Real.rpow_one] at h
    exact h

  have hfirst :
      lam0 * α - (1 / d₀) * Real.log (1 - p + p * Real.exp (lam0 * d₀)) =
        (1 / d₀) * LimitedPriceChanges.LowerBound.klBer α p := by
    rw [hexp0, ← hB_def, hlam0_def]
    unfold LimitedPriceChanges.LowerBound.klBer
    rw [hlog_z, hlog_recip]
    ring

  have hsecond :
      lam0 * α - (1 / d₀) * Real.log (1 - p + p * Real.exp (lam0 * d₀)) -
          (lam0 * α - (1 / d) * Real.log (1 - p + p * Real.exp (lam0 * d))) =
        (1 / d) * Real.log (1 - p + p * z ^ (d / d₀)) -
          (1 / d₀) * Real.log B := by
    rw [hexp0, hexpd, ← hB_def]
    ring

  have hthird :
      1 - p + p * z ^ (d / d₀) ≤ z ^ (d / d₀ - 1) * B := by
    rw [hzpow, hB_def]
    have hnonneg : 0 ≤ (z ^ (d / d₀ - 1) - 1) * (1 - p) :=
      mul_nonneg (sub_nonneg.mpr hpow1) h1p.le
    nlinarith [hnonneg]

  have hC_pos : 0 < z ^ (d / d₀ - 1) :=
    Real.rpow_pos_of_pos hz_pos _

  have hL_pos : 0 < 1 - p + p * z ^ (d / d₀) := by
    have hnonneg : 0 ≤ p * z ^ (d / d₀) :=
      mul_nonneg hp.le (Real.rpow_pos_of_pos hz_pos _).le
    linarith

  have hlog_third :
      Real.log (1 - p + p * z ^ (d / d₀)) ≤
        (d / d₀ - 1) * Real.log z + Real.log B := by
    calc
      Real.log (1 - p + p * z ^ (d / d₀)) ≤
          Real.log (z ^ (d / d₀ - 1) * B) :=
        Real.log_le_log hL_pos hthird
      _ = Real.log (z ^ (d / d₀ - 1)) + Real.log B := by
        rw [Real.log_mul (ne_of_gt hC_pos) hB_ne]
      _ = (d / d₀ - 1) * Real.log z + Real.log B := by
        rw [Real.log_rpow hz_pos]

  refine ⟨hfirst, hsecond, hthird, ?_, ?_⟩
  · rw [hsecond]
    calc
      (1 / d) * Real.log (1 - p + p * z ^ (d / d₀)) -
            (1 / d₀) * Real.log B
          ≤ (1 / d) * ((d / d₀ - 1) * Real.log z + Real.log B) -
            (1 / d₀) * Real.log B :=
        sub_le_sub_right
          (mul_le_mul_of_nonneg_left hlog_third
            (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hd.le))
          ((1 / d₀) * Real.log B)
      _ = (1 / d₀ - 1 / d) * (Real.log z - Real.log B) := by
        field_simp [ne_of_gt hd, ne_of_gt hd₀] <;> ring
  · rw [hlog_z]
    ring

