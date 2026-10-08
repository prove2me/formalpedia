-- Prove2me | solution 1 for OnlineRandomization.Tightness.params_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:09:23.174984+00:00
-- url     : https://prove2.me/submissions/56f5a098-f19c-46d9-b90a-85997e1066ac

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

set_option autoImplicit false

lemma params6ab08a0c_aux (α β C s : ℝ) (hβ : 1 < β) (hβα : β ≤ α) (hC : C < α * β)
    (h2 : 2 ≤ s) (h1 : (α + β) / (2 * (β - 1)) ≤ s)
    (h3 : (α - 1) * (|C| + 1) / (α * β - C) ≤ s) :
    max (((1 + (2 * s - 1) * (2 * s * β - 1) - 2 * α) /
          ((2 * s - 2) * (α + 2 * s - 1))) ^ 2) C ≤
        (2 * s * α * β + α - 1) / (α + 2 * s - 1) ∧
      1 ≤ (1 + (2 * s - 1) * (2 * s * β - 1) - 2 * α) /
          ((2 * s - 2) * (α + 2 * s - 1)) ∧
      (1 + (2 * s - 1) * (2 * s * β - 1) - 2 * α) /
          ((2 * s - 2) * (α + 2 * s - 1)) ≤ (2 * s * α * β + α - 1) / (α + 2 * s - 1) ∧
      α * ((1 + (2 * s - 1) * (2 * s * β - 1) - 2 * α) /
          ((2 * s - 2) * (α + 2 * s - 1)) - 1) ≤
        (2 * s * α * β + α - 1) / (α + 2 * s - 1) -
          (1 + (2 * s - 1) * (2 * s * β - 1) - 2 * α) /
          ((2 * s - 2) * (α + 2 * s - 1)) := by
  set m := (1 + (2 * s - 1) * (2 * s * β - 1) - 2 * α) /
          ((2 * s - 2) * (α + 2 * s - 1)) with hm_def
  set M := (2 * s * α * β + α - 1) / (α + 2 * s - 1) with hM_def
  have hD : 0 < α + 2 * s - 1 := by linarith
  have hE : 0 < 2 * s - 2 := by linarith
  have hb1 : 0 < β - 1 := by linarith
  have hab : 0 < α * β - C := by linarith
  have hEne : (2 * s - 2) ≠ 0 := hE.ne'
  have hDne : (α + 2 * s - 1) ≠ 0 := hD.ne'
  have hED : (2 * s - 2) * (α + 2 * s - 1) ≠ 0 := mul_ne_zero hEne hDne
  -- item: 1 ≤ m
  have e1 : m - 1 = 2 * s * (2 * (β - 1) * s + 2 - β - α) / ((2 * s - 2) * (α + 2 * s - 1)) := by
    rw [hm_def, div_sub_one hED, div_eq_div_iff hED hED]; ring
  have g1 : 0 ≤ 2 * (β - 1) * s + 2 - β - α := by
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  have i1 : 1 ≤ m := by
    have : 0 ≤ m - 1 := by rw [e1]; apply div_nonneg <;> [nlinarith; positivity]
    linarith
  -- item: m ≤ M
  have e2 : M - m = 2 * s * (2 * β * (α - 1) * s + β + α - 2 * α * β) /
      ((2 * s - 2) * (α + 2 * s - 1)) := by
    rw [hm_def, hM_def, div_sub_div _ _ hDne hED, div_eq_div_iff (mul_ne_zero hDne hED) hED]; ring
  have g2 : 0 ≤ 2 * β * (α - 1) * s + β + α - 2 * α * β := by
    have hα1 : 0 ≤ α - 1 := by linarith
    have : 2 * β * (α - 1) * 2 ≤ 2 * β * (α - 1) * s := by
      apply mul_le_mul_of_nonneg_left h2; positivity
    nlinarith
  have i2 : m ≤ M := by
    have : 0 ≤ M - m := by rw [e2]; apply div_nonneg <;> [nlinarith; positivity]
    linarith
  -- item: α (m - 1) ≤ M - m
  have e3 : M - m - α * (m - 1) = 2 * s * (α - β) * (2 * s + α - 1) /
      ((2 * s - 2) * (α + 2 * s - 1)) := by
    rw [e1, e2, mul_div_assoc', div_sub_div_same]; congr 1; ring
  have i3 : α * (m - 1) ≤ M - m := by
    have : 0 ≤ M - m - α * (m - 1) := by
      rw [e3]; apply div_nonneg
      · have : 0 ≤ α - β := by linarith
        have : 0 ≤ 2 * s + α - 1 := by linarith
        positivity
      · positivity
    linarith
  -- item: C ≤ M
  have e4 : M - C = (2 * s * (α * β - C) + (α - 1) * (1 - C)) / (α + 2 * s - 1) := by
    rw [hM_def]; field_simp; ring
  have i4 : C ≤ M := by
    rw [div_le_iff₀ hab] at h3
    have hα1 : 0 ≤ α - 1 := by linarith
    have hCabs : (α - 1) * (C - 1) ≤ (α - 1) * (|C| + 1) := by
      apply mul_le_mul_of_nonneg_left _ hα1
      have := le_abs_self C; linarith
    have : 0 ≤ M - C := by
      rw [e4]; apply div_nonneg _ hD.le
      nlinarith
    linarith
  -- item: m ^ 2 ≤ M
  have e5 : M - m ^ 2 =
      (8 * s * (s - 1) ^ 2 * (β - 1) ^ 3 + (α - β) * s *
        (64 + 128 * (s - 2) + 80 * (s - 2) ^ 2 + 16 * (s - 2) ^ 3
          + 80 * (β - 1) + 152 * (β - 1) * (s - 2) + 88 * (β - 1) * (s - 2) ^ 2
          + 16 * (β - 1) * (s - 2) ^ 3
          + 16 * (β - 1) ^ 2 + 32 * (β - 1) ^ 2 * (s - 2) + 16 * (β - 1) ^ 2 * (s - 2) ^ 2
          + 8 * (α - β) + 20 * (α - β) * (s - 2) + 8 * (α - β) * (s - 2) ^ 2
          + 8 * (α - β) * (β - 1) + 16 * (α - β) * (β - 1) * (s - 2)
          + 8 * (α - β) * (β - 1) * (s - 2) ^ 2)) /
      ((2 * s - 2) ^ 2 * (α + 2 * s - 1) ^ 2) := by
    rw [hm_def, hM_def, div_pow, div_sub_div _ _ hDne (pow_ne_zero 2 hED),
      div_eq_div_iff (mul_ne_zero hDne (pow_ne_zero 2 hED))
        (mul_ne_zero (pow_ne_zero 2 hEne) (pow_ne_zero 2 hDne))]
    ring
  have i5 : m ^ 2 ≤ M := by
    have hu : 0 ≤ s - 2 := by linarith
    have hd : 0 ≤ α - β := by linarith
    have hs1 : 0 ≤ s - 1 := by linarith
    have hs0 : 0 ≤ s := by linarith
    have : 0 ≤ M - m ^ 2 := by
      rw [e5]; apply div_nonneg _ (by positivity)
      positivity
    linarith
  exact ⟨max_le i5 i4, i1, i2, i3⟩

open Filter OnlineRandomization.Tightness in
theorem solution (α β C : ℝ) (hβ : 1 < β) (hβα : β ≤ α) (hC : C < α * β) :
    ∀ᶠ t : ℕ in atTop,
      max (paramSmall α β t ^ 2) C ≤ paramLarge α β t ∧
      1 ≤ paramSmall α β t ∧
      paramSmall α β t ≤ paramLarge α β t ∧
      α * (paramSmall α β t - 1) ≤ paramLarge α β t - paramSmall α β t := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 : ℝ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop ((α + β) / (2 * (β - 1))),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop ((α - 1) * (|C| + 1) / (α * β - C))]
    with t h2 h1 h3
  exact params6ab08a0c_aux α β C (t : ℝ) hβ hβα hC h2 h1 h3
