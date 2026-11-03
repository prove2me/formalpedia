-- Prove2me | solution 1 for RegevLWE.Hyperplane.expectation_lt_nine_tenths
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T21:35:24.586244+00:00
-- url     : https://prove2.me/submissions/986703a7-9156-4fcd-b221-cca28cca05a6

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Theorems.Thm_RegevLWE_Hyperplane_expectation_chain
import Theorems.Thm_RegevLWE_Hyperplane_rhoLattice_poisson

open RegevLWE.Hyperplane

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε r : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (hr : 0 < r) (h : Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam L ε ≤ r)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    (∑' x : L, discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
      1 / Real.sqrt 2 * (1 + ε) ∧
    1 / Real.sqrt 2 * (1 + ε) < 9 / 10 := by
  have h_chain := (expectation_chain L hε hr h w hw).2.2.2
  have h_poiss := (rhoLattice_poisson L hr).2
  have h_cov_pos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have h_num_pos : 0 < (ZLattice.covolume L)⁻¹ * r ^ n :=
    mul_pos (inv_pos.mpr h_cov_pos) (pow_pos hr n)
  have h_rho_pos : 0 < rhoLattice r L := lt_of_lt_of_le h_num_pos h_poiss
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_div : (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) ≤
      1 / Real.sqrt 2 := by
    rw [div_le_div_iff₀ (mul_pos h_sqrt2_pos h_rho_pos) h_sqrt2_pos]
    have := mul_le_mul_of_nonneg_left h_poiss (le_of_lt h_sqrt2_pos)
    linarith
  have h_first :
      (∑' x : L, discreteGaussian L r x *
          Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
        1 / Real.sqrt 2 * (1 + ε) :=
    le_trans h_chain (mul_le_mul_of_nonneg_right h_div (by linarith))
  have h_sqrt2_gt : (11 / 9 : ℝ) < Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 11 / 9)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h_second : 1 / Real.sqrt 2 * (1 + ε) < 9 / 10 := by
    have h_step1 : 1 / Real.sqrt 2 * (1 + ε) ≤ (1 + 1 / 10) / Real.sqrt 2 := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h_sqrt2_pos)
    have h_step2 : (1 + 1 / 10) / Real.sqrt 2 < 9 / 10 := by
      rw [div_lt_iff₀ h_sqrt2_pos]
      linarith
    exact lt_of_le_of_lt h_step1 h_step2
  exact ⟨h_first, h_second⟩
