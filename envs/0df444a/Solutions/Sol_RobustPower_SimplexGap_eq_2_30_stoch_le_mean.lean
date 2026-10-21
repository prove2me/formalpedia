-- Prove2me | solution 1 for RobustPower.SimplexGap.eq_2_30_stoch_le_mean
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:33:28.785847+00:00
-- url     : https://prove2.me/submissions/5cbc73e0-bc0a-41da-9070-c5504fa483f7

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

set_option autoImplicit false

open MeasureTheory RobustPower.SimplexGap

theorem solution (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    StochFeasible μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅
        (0 : Fin 0 → ℝ) b ∧
      zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
          (lastUnit n) b ∅ ∅ ≤ ((∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ : ℝ) : EReal) := by
  obtain ⟨hmeas, hrange, -⟩ := hμb
  have hmem : ∀ ω, b ω ∈ cornerSimplex n := fun ω => hrange ▸ Set.mem_range_self ω
  have hfeas : StochFeasible μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b
      ∅ ∅ (0 : Fin 0 → ℝ) b := by
    refine ⟨⟨le_refl _, by simp⟩, ?_, fun ω => ⟨⟨(hmem ω).2, by simp⟩, by simp⟩⟩
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    obtain ⟨h1, h2⟩ := hmem ω
    have hi : b ω i ≤ ∑ j, b ω j :=
      Finset.single_le_sum (f := fun j => b ω j) (fun j _ => h2 j) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg (h2 i)]
    linarith
  refine ⟨hfeas, ?_⟩
  have hd : ∀ y : Fin n → ℝ, lastUnit n ⬝ᵥ y = y ⟨n - 1, by omega⟩ := by
    intro y
    unfold dotProduct
    rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
    · simp [lastUnit]
    · intro j _ hj
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      simp [lastUnit, this]
    · simp
  unfold zStoch
  refine iInf_le_of_le (0 : Fin 0 → ℝ) (iInf_le_of_le b (iInf_le_of_le hfeas (le_of_eq ?_)))
  have : ∫ ω, lastUnit n ⬝ᵥ b ω ∂μ = ∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ := by
    congr 1; ext ω; exact hd _
  rw [this]
  simp
