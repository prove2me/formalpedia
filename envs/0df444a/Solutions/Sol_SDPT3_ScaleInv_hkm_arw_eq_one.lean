-- Prove2me | solution 1 for SDPT3.ScaleInv.hkm_arw_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:26:24.692318+00:00
-- url     : https://prove2.me/submissions/4266d772-dccf-45b6-8392-9a50544bed18

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

open Matrix SDPT3.ScaleInv
set_option maxHeartbeats 1000000

private theorem metric_hkm {k : ℕ} (z : Fin (k + 1) → ℝ) (hz : socInt z) :
    GHKM z * Jbar k * GHKM z = gammaSq z • Jbar k := by
  have hg : 0 < gam z := Real.sqrt_pos.2 hz.2
  have hgs : gam z ^ 2 = gammaSq z := Real.sq_sqrt (le_of_lt hz.2)
  have hd : gam z + z 0 ≠ 0 := ne_of_gt (add_pos hg hz.1)
  have hs : gammaSq z = z 0 ^ 2 - ∑ i : Fin k, z i.succ ^ 2 := by
    simp [gammaSq, Jbar, mulVec_diagonal, dotProduct, Fin.sum_univ_succ, pow_two,
      ← Finset.sum_neg_distrib, sub_eq_add_neg]
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  all_goals
    simp [Matrix.mul_apply, Jbar, GHKM, Fin.sum_univ_succ,
      Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _), diagonal_apply, Matrix.smul_apply,
      add_mul, mul_add, ite_mul, mul_ite, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq]
  · rw [hs]
    simp [pow_two, sub_eq_add_neg]
  · simp only [mul_div_assoc, ← mul_assoc, ← pow_two, ← Finset.sum_mul, ← Finset.sum_div]
    have hh : ∑ r : Fin k, z r.succ^2 = z 0^2 - gam z^2 := by rw [hs] at hgs; linarith
    rw [hh]
    field_simp
    ring
  · simp only [div_mul_eq_mul_div, mul_assoc, ← pow_two, ← Finset.mul_sum, ← Finset.sum_div]
    have hh : ∑ r : Fin k, z r.succ^2 = z 0^2 - gam z^2 := by rw [hs] at hgs; linarith
    rw [hh]
    field_simp
    ring
  · have ht : (∑ r : Fin k, z i.succ * z r.succ / (gam z + z 0) *
        (z r.succ * z j.succ / (gam z + z 0))) =
        z i.succ * z j.succ / (gam z + z 0)^2 * ∑ r : Fin k, z r.succ^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      field_simp
      <;> ring
    have hh : ∑ r : Fin k, z r.succ^2 = z 0^2 - gam z^2 := by rw [hs] at hgs; linarith
    rw [ht, hh, ← hgs]
    split_ifs <;> field_simp <;> ring

theorem solution {k : ℕ} (z : Fin (k + 1) → ℝ) (hz : socInt z) :
    IsUnit (GHKM z).det ∧ GHKM z *ᵥ e1 k = z ∧ arw ((GHKM z)⁻¹ *ᵥ z) = 1 := by
  have hm := metric_hkm z hz
  have he : GHKM z *ᵥ e1 k = z := by
    ext a
    by_cases ha : a = 0 <;> simp [e1, GHKM, ha]
  have hl : (gammaSq z)⁻¹ • (Jbar k * GHKM z * Jbar k) * GHKM z = 1 := by
    rw [smul_mul]
    have hr : Jbar k * GHKM z * Jbar k * GHKM z = Jbar k * (GHKM z * Jbar k * GHKM z) := by
      simp only [mul_assoc]
    rw [hr, hm]
    have hj : Jbar k * Jbar k = 1 := by
      simp only [Jbar, diagonal_mul_diagonal]
      ext i j
      by_cases hi : i = 0 <;> simp [hi, diagonal_apply, Matrix.one_apply]
    simp only [Matrix.mul_smul, hj, smul_smul, inv_mul_cancel₀ hz.2.ne', one_smul]
  have hu := isUnit_det_of_left_inverse hl
  refine ⟨hu, he, ?_⟩
  have hv : (GHKM z)⁻¹ *ᵥ z = e1 k := by
    calc
      _ = (GHKM z)⁻¹ *ᵥ (GHKM z *ᵥ e1 k) := by rw [he]
      _ = e1 k := by rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  rw [hv]
  ext a b
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [arw, e1, ha, hb, Ne.symm, Pi.single_apply, Matrix.one_apply]

#print axioms solution
