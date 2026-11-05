-- Prove2me | solution 1 for PrimalDualPricing.Regret.primal_dual_regret_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:59:06.803665+00:00
-- url     : https://prove2.me/submissions/1ffd5656-855a-4b87-9f74-2354d9cd0531
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System
import Theorems.Thm_PrimalDualPricing_Regret_proposition_2
import Theorems.Thm_PrimalDualPricing_Regret_proposition_3

open MeasureTheory ProbabilityTheory PrimalDualPricing.Regret

/-- If `log n ≥ 1`, raising the log power only increases the bound (for a nonnegative constant). -/
lemma pdp_goal_mono (C a b : ℝ) (hab : a ≤ b) (n : ℕ) (hn : 3 ≤ n) (R : ℝ)
    (hR : R ≤ C * Real.log n ^ a * (n : ℝ) ^ (-(1 / 2 : ℝ))) :
    R ≤ max C 0 * Real.log n ^ b * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog1 : 1 ≤ Real.log n := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have : Real.exp 1 ≤ (n : ℝ) := le_trans (Real.exp_one_lt_d9.le.trans (by norm_num)) h3
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) this
  have hpow : Real.log n ^ a ≤ Real.log n ^ b := Real.rpow_le_rpow_of_exponent_le hlog1 hab
  have hpa : 0 ≤ Real.log n ^ a := Real.rpow_nonneg (by linarith) a
  have hq : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
  have hC : 0 ≤ max C 0 := le_max_right _ _
  calc R ≤ C * Real.log n ^ a * (n : ℝ) ^ (-(1 / 2 : ℝ)) := hR
    _ ≤ max C 0 * Real.log n ^ a * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpa
    _ ≤ max C 0 * Real.log n ^ b * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul_of_nonneg_left hpow hC

theorem solution {M : ℕ} (hM : 0 < M) (S : Setting M) :
    ∀ δ : ℝ, 0 < δ → ∃ eps : ℝ, 0 < eps ∧ ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          S.regret eps n N ≤ C * Real.log n ^ (2 + δ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  intro δ hδ
  rcases S.zstar_nonneg.eq_or_lt with hz | hz
  · obtain ⟨ε₀, hε₀, h⟩ := proposition_2 hM S hz.symm
    set eps := min (ε₀ / 2) (δ / 16) with heps
    have he0 : 0 < eps := lt_min (by linarith) (by linarith)
    have he1 : eps < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have he2 : 16 * eps ≤ δ := by have := min_le_right (ε₀ / 2) (δ / 16); linarith
    obtain ⟨C, hC⟩ := h eps he0 he1
    refine ⟨eps, he0, max C 0, ?_⟩
    intro Ω _ _ N hN n hn
    exact pdp_goal_mono C _ _ (by linarith) n hn _ (hC Ω N hN n hn)
  · obtain ⟨ε₀, hε₀, h⟩ := proposition_3 hM S hz
    set eps := min (ε₀ / 2) (δ / 18) with heps
    have he0 : 0 < eps := lt_min (by linarith) (by linarith)
    have he1 : eps < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have he2 : 18 * eps ≤ δ := by have := min_le_right (ε₀ / 2) (δ / 18); linarith
    obtain ⟨C, hC⟩ := h eps he0 he1
    refine ⟨eps, he0, max C 0, ?_⟩
    intro Ω _ _ N hN n hn
    exact pdp_goal_mono C _ _ (by linarith) n hn _ (hC Ω N hN n hn)
