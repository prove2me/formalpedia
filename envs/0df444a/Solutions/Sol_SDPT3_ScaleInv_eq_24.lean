-- Prove2me | solution 1 for SDPT3.ScaleInv.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:30:14.804463+00:00
-- url     : https://prove2.me/submissions/705586bc-d9e6-4c56-a3e1-3e08f43a229f

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

private theorem hkm {k : ℕ} (z : Fin (k + 1) → ℝ) (hz : socInt z) :
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

private theorem jb_sq (k : ℕ) : Jbar k * Jbar k = 1 := by
  simp only [Jbar, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = 0 <;> simp [h, diagonal_apply, Matrix.one_apply]

private theorem hkm_sym {k : ℕ} (z : Fin (k+1) → ℝ) : (GHKM z)ᵀ = GHKM z := by
  ext a b
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [GHKM, transpose_apply, ha, hb, mul_comm, eq_comm]

private theorem arrow_expand {k : ℕ} (v : Fin (k+1) → ℝ) :
    arw v = v 0 • J k + vecMulVec (e1 k) v + vecMulVec v (e1 k) := by
  ext a b
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [arw, SDPT3.ScaleInv.J, Jbar, diagonal_apply, e1, ha, hb, Ne.symm, Matrix.smul_apply,
      vecMulVec_apply, Pi.single_apply, eq_comm] <;> split_ifs <;> ring

private theorem hkm_formula {k : ℕ} (x z : Fin (k + 1) → ℝ) (hz : socInt z) :
    (calE (GHKM z) z)⁻¹ * calF (GHKM z) x = (GHKM z)⁻¹ * arw (GHKM z *ᵥ x) * (GHKM z)⁻¹ ∧
      (GHKM z)⁻¹ * arw (GHKM z *ᵥ x) * (GHKM z)⁻¹ =
        (gammaSq z)⁻¹ • ((x ⬝ᵥ z) • J k + vecMulVec x (Jbar k *ᵥ z) +
          vecMulVec (Jbar k *ᵥ z) x) := by
  obtain ⟨hu, he, ha⟩ := hkm z hz
  have hinv : (GHKM z)⁻¹ = (gammaSq z)⁻¹ • (Jbar k * GHKM z * Jbar k) := by
    have hm := metric_hkm z hz
    have hl : ((gammaSq z)⁻¹ • (Jbar k * GHKM z * Jbar k)) * GHKM z = 1 := by
      simp only [smul_mul, mul_assoc]
      rw [← mul_assoc (GHKM z), hm]
      simp only [Matrix.mul_smul, jb_sq, smul_smul, inv_mul_cancel₀ hz.2.ne', one_smul]
    calc
      _ = 1 * (GHKM z)⁻¹ := (one_mul _).symm
      _ = (((gammaSq z)⁻¹ • (Jbar k * GHKM z * Jbar k)) * GHKM z) * (GHKM z)⁻¹ := by rw [hl]
      _ = _ := by rw [mul_assoc, mul_nonsing_inv _ hu, mul_one]
  have hij : (GHKM z)⁻¹ * J k * (GHKM z)⁻¹ = (gammaSq z)⁻¹ • J k := by
    conv_lhs => rw [hinv]
    simp only [SDPT3.ScaleInv.J, mul_neg, neg_mul, Matrix.smul_mul, Matrix.mul_smul, mul_assoc, jb_sq, one_mul]
    rw [← mul_assoc (GHKM z), ← mul_assoc (GHKM z * Jbar k), metric_hkm z hz]
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc, jb_sq, one_mul,
      ← smul_smul, smul_neg, neg_inj]
    congr 1
    field_simp
    simp [smul_smul, mul_one, hz.2.ne']
  have hie : (GHKM z)⁻¹ *ᵥ e1 k = (gammaSq z)⁻¹ • (Jbar k *ᵥ z) := by
    rw [hinv, Matrix.smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    have hj : Jbar k *ᵥ e1 k = e1 k := by ext a; simp [Jbar, e1, mulVec_diagonal, Pi.single_apply]; split_ifs <;> simp_all
    rw [hj, he]
  have hiv : (GHKM z)⁻¹ *ᵥ (GHKM z *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hv0 : (GHKM z *ᵥ x) 0 = x ⬝ᵥ z := by
    simp [GHKM, mulVec, dotProduct, mul_comm]
  have his : ((GHKM z)⁻¹)ᵀ = (GHKM z)⁻¹ := by rw [transpose_nonsing_inv, hkm_sym]
  refine ⟨?_, ?_⟩
  · simp only [calE, calF, ha, one_mul, mul_assoc]
  · rw [arrow_expand, mul_add, mul_add, add_mul, add_mul, Matrix.mul_smul, Matrix.smul_mul, hij,
      mul_vecMulVec, vecMulVec_mul, mul_vecMulVec, vecMulVec_mul]
    simp only [← mulVec_transpose, his, hie, hiv, hv0, smul_vecMulVec, vecMulVec_smul, smul_smul,
      smul_add]
    module


theorem solution {k m : ℕ} (Ai : Matrix (Fin (k + 1)) (Fin m) ℝ) (x z : Fin (k + 1) → ℝ)
    (hz : socInt z) :
    Mblock (GHKM z) Ai x z =
      ((x ⬝ᵥ z) / gammaSq z) • (Aiᵀ * J k * Ai) +
        vecMulVec (Aiᵀ *ᵥ x) (Aiᵀ *ᵥ ((gammaSq z)⁻¹ • (Jbar k *ᵥ z))) +
        vecMulVec (Aiᵀ *ᵥ ((gammaSq z)⁻¹ • (Jbar k *ᵥ z))) (Aiᵀ *ᵥ x) := by
  rw [Mblock, (hkm_formula x z hz).1, (hkm_formula x z hz).2]
  simp only [smul_add]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, smul_add,
    mul_vecMulVec, vecMulVec_mul, ← mulVec_transpose, transpose_transpose,
    Matrix.mulVec_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, div_eq_mul_inv]
  module

#print axioms solution
