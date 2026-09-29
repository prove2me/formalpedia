-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.corollary2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:33:46.671946+00:00
-- url     : https://prove2.me/submissions/67ed0896-6a46-47f5-aa61-aabee2094b5a

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

theorem aux_c2_sum_eq (α : ℝ) (hα0 : 0 ≤ α) (n : ℕ) :
    ∑ k ∈ Finset.range n, ENNReal.ofReal (α ^ k) =
      ENNReal.ofReal (∑ k ∈ Finset.range n, α ^ k) := by
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro k _
  positivity

theorem aux_c2_measurable_G (κ : Costs) : Measurable (fun y : ℝ => ENNReal.ofReal (G κ y)) := by
  unfold G
  fun_prop

end XinGoldbergTBS.Asymptotic

open XinGoldbergTBS.Asymptotic
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
          ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal
              (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P
      ≤ OPT μ κ L₀ L ∧
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          ∑ k ∈ Finset.range (L - L₀), ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal (G κ (I ω
                + ∑ i ∈ Finset.range k, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)
                + qN L₀ L q ω k - ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω)) ∂P
      ≤ ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
          ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) *
            ∫⁻ ω, ENNReal.ofReal
              (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P := by
  set X := ∫⁻ ω, ENNReal.ofReal
    (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P with hX
  have hA : ENNReal.ofReal ((1 - α) / (1 - α ^ L)) *
      ∑ k ∈ Finset.range L, ENNReal.ofReal (α ^ k) * X = X := by
    have h1 : α ^ L < 1 := pow_lt_one₀ hα0.le hα1 (by omega)
    have hpos : 0 ≤ (1 - α) / (1 - α ^ L) := div_nonneg (by linarith) (by linarith)
    rw [← Finset.sum_mul, ← mul_assoc, aux_c2_sum_eq α hα0.le, ← ENNReal.ofReal_mul hpos]
    have : (1 - α) / (1 - α ^ L) * ∑ k ∈ Finset.range L, α ^ k = 1 := by
      rw [div_mul_eq_mul_div, mul_neg_geom_sum, div_self (by linarith)]
    rw [this, ENNReal.ofReal_one, one_mul]
  have hB : ∀ k ∈ Finset.range (L - L₀),
      ∫⁻ ω, ENNReal.ofReal (G κ (I ω
                + ∑ i ∈ Finset.range k, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)
                + qN L₀ L q ω k - ∑ i ∈ Finset.range (L₀ + 1), D (k + i) ω)) ∂P = X := by
    intro k hk
    have hk' : k < L - L₀ := Finset.mem_range.mp hk
    have h2 := ((hw.stationary ⟨k, hk'⟩).comp (aux_c2_measurable_G κ)).lintegral_eq
    simp only [Function.comp_def] at h2
    have hq : ∀ ω, qN L₀ L q ω k = q ω ⟨k, hk'⟩ := fun ω => by simp [qN, hk']
    simp_rw [hq]
    exact h2
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact hw.opt_ge
  · rw [hA, Finset.sum_congr rfl (fun k hk => by rw [hB k hk])]
    rw [← Finset.sum_mul, ← mul_assoc, aux_c2_sum_eq α hα0.le,
      ← ENNReal.ofReal_mul (by linarith)]
    gcongr
    calc ENNReal.ofReal ((1 - α) * ∑ k ∈ Finset.range (L - L₀), α ^ k) * X
        ≤ 1 * X := by
          gcongr
          rw [mul_neg_geom_sum]
          apply ENNReal.ofReal_le_one.mpr
          have : 0 ≤ α ^ (L - L₀) := by positivity
          linarith
      _ = X := one_mul X
