-- Prove2me | solution 1 for burau_rho_T
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T23:47:06.78799+00:00
-- url     : https://prove2.me/submissions/ffa3378c-1d05-42fe-8ae3-5779cceda77e

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

open Matrix

namespace BurauNC

theorem q_shift_ (M : M2) (h : M 0 0 ≠ 0) (j : ℤ) :
    -(((M * Tm j) 0 1) / ((M * Tm j) 0 0)) = -(M 0 1 / M 0 0) - j := by
  have h00 : (M * Tm j) 0 0 = M 0 0 := by
    simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (M * Tm j) 0 1 = M 0 1 + M 0 0 * j := by
    simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h00, h01, Int.add_mul_ediv_left (M 0 1) j h]
  ring

theorem Tm_add_ (a b : ℤ) : Tm a * Tm b = Tm (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem baseQ_mul_Tm_ (M : M2) (hd : M.det = 1) (h0 : M 0 0 = 0) (j : ℤ) :
    baseQ (M * Tm j) = baseQ M * liftT ^ j := by
  have hdet : M 0 1 * M 1 0 = -1 := by
    have h2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hd
    rw [h0] at h2
    simp only [zero_mul, zero_sub] at h2
    linarith
  have hone : M 0 1 * (-(M 1 0)) = 1 := by
    rw [mul_neg, hdet]
    ring
  have h01 : (M * Tm j) 0 1 = M 0 1 := by
    simp [Tm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have h11 : (M * Tm j) 1 1 = M 1 1 + M 1 0 * j := by
    simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [baseQ, baseQ]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h10 : M 1 0 = -1 := by linarith
    have hb : ¬ (M 0 1 = -1) := by rw [h1]; norm_num
    have hbj : ¬ ((M * Tm j) 0 1 = -1) := by rw [h01, h1]; norm_num
    simp only [hb, hbj, if_false]
    rw [h11, h10]
    rw [show -(M 1 1 + -1 * j) = -M 1 1 + j by ring, _root_.zpow_add, mul_assoc]
  · have h10 : M 1 0 = 1 := by linarith
    have hb : M 0 1 = -1 := h1
    have hbj : (M * Tm j) 0 1 = -1 := by rw [h01, h1]
    simp only [hb, hbj, if_true]
    rw [h11, h10]
    rw [show M 1 1 + 1 * j = M 1 1 + j by ring, _root_.zpow_add, mul_assoc]

theorem rhoIter_T_ (k : ℕ) : ∀ (M : M2) (j : ℤ), M.det = 1 → (M 0 0).natAbs ≤ k →
    rhoIter k (M * Tm j) = rhoIter k M * liftT ^ j := by
  induction k with
  | zero =>
      intro M j hd hk
      have h0 : M 0 0 = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp only [rhoIter]
      exact baseQ_mul_Tm_ M hd h0 j
  | succ k ih =>
      intro M j hd hk
      by_cases h0 : M 0 0 = 0
      · have h00 : (M * Tm j) 0 0 = M 0 0 := by
          simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]
        have h0j : (M * Tm j) 0 0 = 0 := by rw [h00, h0]
        simp only [rhoIter, if_pos h0, if_pos h0j]
        exact baseQ_mul_Tm_ M hd h0 j
      · have h00 : (M * Tm j) 0 0 = M 0 0 := by
          simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]
        have h0j : ¬ ((M * Tm j) 0 0 = 0) := by rw [h00]; exact h0
        have hinner : ((M * Tm j) * Tm (-((M * Tm j) 0 1 / (M * Tm j) 0 0))) * Sm =
            (M * Tm (-(M 0 1 / M 0 0))) * Sm := by
          rw [q_shift_ M h0 j]
          congr 1
          rw [Matrix.mul_assoc, Tm_add_]
          congr 1
          ring
        have hexp' : (M * Tm j) 0 1 / (M * Tm j) 0 0 = M 0 1 / M 0 0 + j := by
          have h := q_shift_ M h0 j
          linarith
        simp only [rhoIter, if_neg h0, if_neg h0j]
        rw [hinner, hexp']
        rw [_root_.zpow_add]
        group

end BurauNC

theorem solution (M : BurauNC.M2) (j : ℤ) (hd : M.det = 1) :
    BurauNC.rho (M * BurauNC.Tm j) = BurauNC.rho M * BurauNC.liftT ^ j := by
  simp only [BurauNC.rho]
  rw [show (M * BurauNC.Tm j) 0 0 = M 0 0 by
    simp [BurauNC.Tm, Matrix.mul_apply, Fin.sum_univ_two]]
  exact BurauNC.rhoIter_T_ (M 0 0).natAbs M j hd le_rfl
