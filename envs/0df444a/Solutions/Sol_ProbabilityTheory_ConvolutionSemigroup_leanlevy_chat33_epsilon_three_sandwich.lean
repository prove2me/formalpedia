-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_epsilon_three_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:55:21.246924+00:00
-- url     : https://prove2.me/submissions/c01d9611-2f56-46a6-b3cf-d21756c21ade

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {M : ℝ} (hM : 0 ≤ M)
    {A B : ℕ → ℝ} {a b : ℕ → ℕ → ℝ} {c : ℕ → ℝ} {L : ℝ}
    (hA : Tendsto A atTop (𝓝 L))
    (hB : Tendsto B atTop (𝓝 0))
    (ha : ∀ n, Tendsto (a n) atTop (𝓝 (A n)))
    (hb : ∀ n, Tendsto (b n) atTop (𝓝 (B n)))
    (herr : ∀ n k, |c k - a n k| ≤ M * b n k) :
    Tendsto c atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hδ : 0 < ε / (6 * (M + 1)) := by positivity
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hA) (ε / 3) hε3
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hB)
    (ε / (6 * (M + 1))) hδ
  let n0 : ℕ := max N1 N2
  have hAn : |A n0 - L| < ε / 3 := by
    have h := hN1 n0 (le_max_left _ _)
    rwa [Real.dist_eq] at h
  have hBn : |B n0| < ε / (6 * (M + 1)) := by
    have h := hN2 n0 (le_max_right _ _)
    rwa [Real.dist_eq, sub_zero] at h
  obtain ⟨K1, hK1⟩ := (Metric.tendsto_atTop.mp (ha n0)) (ε / 3) hε3
  obtain ⟨K2, hK2⟩ := (Metric.tendsto_atTop.mp (hb n0))
    (ε / (6 * (M + 1))) hδ
  refine ⟨max K1 K2, fun k hk => ?_⟩
  have hak : |a n0 k - A n0| < ε / 3 := by
    have h := hK1 k (le_trans (le_max_left _ _) hk)
    rwa [Real.dist_eq] at h
  have hbk : |b n0 k - B n0| < ε / (6 * (M + 1)) := by
    have h := hK2 k (le_trans (le_max_right _ _) hk)
    rwa [Real.dist_eq] at h
  have hBupper : b n0 k ≤ 2 * (ε / (6 * (M + 1))) := by
    have h1 : b n0 k - B n0 ≤ |b n0 k - B n0| := le_abs_self _
    have h2 : B n0 ≤ |B n0| := le_abs_self _
    linarith
  have hMplus : 0 < M + 1 := by linarith
  have hratio : M / (M + 1) ≤ 1 := by
    rw [div_le_one hMplus]
    linarith
  have hMbnd : M * (2 * (ε / (6 * (M + 1)))) ≤ ε / 3 := by
    calc M * (2 * (ε / (6 * (M + 1))))
        = (M / (M + 1)) * (ε / 3) := by field_simp; ring
      _ ≤ 1 * (ε / 3) :=
        mul_le_mul_of_nonneg_right hratio hε3.le
      _ = ε / 3 := one_mul _
  have hsplit : c k - L =
      (c k - a n0 k) + (a n0 k - A n0) + (A n0 - L) := by ring
  have htri : |c k - L| ≤
      |c k - a n0 k| + |a n0 k - A n0| + |A n0 - L| := by
    rw [hsplit]
    have h1 := abs_add_le (c k - a n0 k + (a n0 k - A n0)) (A n0 - L)
    have h2 := abs_add_le (c k - a n0 k) (a n0 k - A n0)
    linarith
  rw [Real.dist_eq]
  have hbnd := mul_le_mul_of_nonneg_left hBupper hM
  linarith [htri, herr n0 k, hbnd, hMbnd, hak, hAn]
