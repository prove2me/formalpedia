-- Prove2me | solution 1 for centered_sampling_coefficient_bernstein_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:18:21.89932+00:00
-- url     : https://prove2.me/submissions/03179121-d9f3-4e8d-b5ad-44627a812696

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_centered_sampling_coefficient_mgf_factorization
import Theorems.Thm_two_point_bernstein_mgf
import Mathlib.Analysis.SpecialFunctions.Exp

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

/-- **Bernstein (variance-scaled) MGF bound** for the centered-sampling coefficient.
For `0 < p ≤ 1`, `‖B‖_∞ ≤ entryScale`, `0 < entryScale`, and
`0 ≤ lam ≤ p / entryScale` (so each per-coordinate increment stays in range),
`E[exp(lam·Coeff)] ≤ exp(lam²·(1-p)/p·‖B‖_F²)`. The exponent carries the TRUE
variance `(1-p)/p·‖B‖_F²` (∼1/p), unlike the Hoeffding/sub-Gaussian range proxy
(∼1/p²). -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (entryScale lam : ℝ)
    (hent : entrySupNorm B ≤ entryScale) (hes : 0 < entryScale)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ p / entryScale) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by
  classical
  have hpne : p ≠ 0 := ne_of_gt hp0
  -- Per-entry bound |B_w| ≤ entryScale.
  have hBw : ∀ w : Fin n₁ × Fin n₂, |B w.1 w.2| ≤ entryScale := by
    intro w
    refine le_trans ?_ hent
    have hbdd2 : ∀ i : Fin n₁, BddAbove (Set.range (fun j : Fin n₂ => |B i j|)) :=
      fun i => Set.Finite.bddAbove (Set.finite_range _)
    have hbdd1 : BddAbove (Set.range (fun i : Fin n₁ => ⨆ j : Fin n₂, |B i j|)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    unfold entrySupNorm
    refine le_trans (le_ciSup (hbdd2 w.1) w.2) ?_
    exact le_ciSup hbdd1 w.1
  -- Key per-coordinate range bound: lam * |B_w| / p ≤ 1.
  have hkey : ∀ w : Fin n₁ × Fin n₂, lam * |B w.1 w.2| / p ≤ 1 := by
    intro w
    rw [div_le_one hp0]
    -- lam * |B_w| ≤ lam * entryScale ≤ p   (lam*entryScale ≤ p from lam ≤ p/entryScale)
    have h1 : lam * |B w.1 w.2| ≤ lam * entryScale :=
      mul_le_mul_of_nonneg_left (hBw w) hlam0
    have h2 : lam * entryScale ≤ p := by
      rw [le_div_iff₀ hes] at hlam; linarith [hlam]
    linarith
  rw [centered_sampling_coefficient_mgf_factorization p B lam]
  -- bound each factor by the per-coord variance exponential.
  have hfac : ∀ w : Fin n₁ × Fin n₂,
      (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
    intro w
    -- Define the two values a (prob p) and b (prob 1-p) of the centered increment.
    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    have hkw := hkey w
    -- centering
    have hcent : p * (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))) = 0 := by
      field_simp; ring
    -- a ≤ 1
    have ha1 : lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) ≤ 1 := by
      have hle : (B w.1 w.2) * (1 - p) ≤ |B w.1 w.2| := by
        calc (B w.1 w.2) * (1 - p) ≤ |B w.1 w.2| * (1 - p) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) h1p
          _ ≤ |B w.1 w.2| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = |B w.1 w.2| := by ring
      have hstep : lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) ≤ lam * |B w.1 w.2| / p := by
        calc lam * (p⁻¹ * (B w.1 w.2) * (1 - p))
            = lam * p⁻¹ * ((B w.1 w.2) * (1 - p)) := by ring
          _ ≤ lam * p⁻¹ * |B w.1 w.2| := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = lam * |B w.1 w.2| / p := by rw [mul_comm lam (p⁻¹), mul_assoc, mul_comm (p⁻¹) (lam * |B w.1 w.2|), div_eq_mul_inv]
      linarith [hstep, hkw]
    -- b ≤ 1
    have hb1 : lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) ≤ 1 := by
      have hle : (B w.1 w.2) * (0 - p) ≤ |B w.1 w.2| := by
        calc (B w.1 w.2) * (0 - p) = -(B w.1 w.2) * p := by ring
          _ ≤ |B w.1 w.2| * p := mul_le_mul_of_nonneg_right (neg_le_abs _) (le_of_lt hp0)
          _ ≤ |B w.1 w.2| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
          _ = |B w.1 w.2| := by ring
      have hstep : lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) ≤ lam * |B w.1 w.2| / p := by
        calc lam * (p⁻¹ * (B w.1 w.2) * (0 - p))
            = lam * p⁻¹ * ((B w.1 w.2) * (0 - p)) := by ring
          _ ≤ lam * p⁻¹ * |B w.1 w.2| := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = lam * |B w.1 w.2| / p := by rw [mul_comm lam (p⁻¹), mul_assoc, mul_comm (p⁻¹) (lam * |B w.1 w.2|), div_eq_mul_inv]
      linarith [hstep, hkw]
    have hH := two_point_bernstein_mgf p
      (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
      (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))
      (le_of_lt hp0) hp1 hcent ha1 hb1
    refine hH.trans ?_
    apply Real.exp_le_exp.mpr
    apply le_of_eq
    field_simp; ring
  calc ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))))
      ≤ ∏ w : Fin n₁ × Fin n₂, Real.exp (lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
        apply Finset.prod_le_prod
        · intro w _
          have h1p : (0:ℝ) ≤ 1 - p := by linarith
          have e1 := mul_nonneg (le_of_lt hp0) (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))).le
          have e2 := mul_nonneg h1p (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))).le
          linarith
        · intro w _; exact hfac w
    _ = Real.exp (∑ w : Fin n₁ × Fin n₂, lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
        rw [← Real.exp_sum]
    _ = Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by
        congr 1
        rw [frobeniusNormSq, ← Fintype.sum_prod_type']
        rw [Finset.mul_sum]
