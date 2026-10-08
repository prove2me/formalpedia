-- Prove2me | solution 1 for SDPT3.ScaleInv.nt_eq_29
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:43:16.511463+00:00
-- url     : https://prove2.me/submissions/7144c0de-fc1e-4c6b-87a2-842ded96954e

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
    simp only [gam]
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


private theorem gs_tail {k : ℕ} (v : Fin (k+1) → ℝ) :
    gammaSq v = v 0 ^ 2 - ∑ i : Fin k, v i.succ ^ 2 := by
  simp [gammaSq, Jbar, mulVec_diagonal, dotProduct, Fin.sum_univ_succ, pow_two,
    ← Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem dot_pos {k : ℕ} (x z : Fin (k+1) → ℝ) (hx : socInt x) (hz : socInt z) :
    0 < x ⬝ᵥ z := by
  have hsx : 0 ≤ ∑ i : Fin k, x i.succ^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsz : 0 ≤ ∑ i : Fin k, z i.succ^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hxx := hx.2
  have hzz := hz.2
  rw [gs_tail] at hxx hzz
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin k => x i.succ) (fun i => z i.succ)
  have hp : (∑ i : Fin k, x i.succ^2) * (∑ i : Fin k, z i.succ^2) < x 0^2 * z 0^2 := by
    calc
      _ ≤ x 0^2 * (∑ i : Fin k, z i.succ^2) := mul_le_mul_of_nonneg_right (by linarith) hsz
      _ < x 0^2 * z 0^2 := mul_lt_mul_of_pos_left (by linarith) (sq_pos_of_pos hx.1)
  have hprod : 0 < x 0 * z 0 := mul_pos hx.1 hz.1
  simp only [dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 0 * z 0 + ∑ i : Fin k, x i.succ * z i.succ)]

private theorem xi_interior {k : ℕ} (x z : Fin (k+1) → ℝ) (hx : socInt x) (hz : socInt z) :
    socInt (xiNT x z) := by
  have hgx : 0 < gam x := Real.sqrt_pos.2 hx.2
  have hgz : 0 < gam z := Real.sqrt_pos.2 hz.2
  have hw : 0 < omegaNT x z := Real.sqrt_pos.2 (div_pos hgz hgx)
  have hw2 : omegaNT x z ^ 2 = gam z / gam x := Real.sq_sqrt (le_of_lt (div_pos hgz hgx))
  have hgx2 : gam x^2 = gammaSq x := Real.sq_sqrt hx.2.le
  have hgz2 : gam z^2 = gammaSq z := Real.sq_sqrt hz.2.le
  have hdot := dot_pos x z hx hz
  constructor
  · simp only [xiNT, if_pos rfl]
    exact add_pos (div_pos hz.1 hw) (mul_pos hw hx.1)
  · have hsum : (∑ i : Fin k, (z i.succ / omegaNT x z - omegaNT x z * x i.succ)^2) =
        (∑ i : Fin k, z i.succ^2) / omegaNT x z ^ 2 -
        2 * (∑ i : Fin k, x i.succ * z i.succ) + omegaNT x z ^ 2 * (∑ i : Fin k, x i.succ^2) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
      <;> ring
    have hcalc : gammaSq (xiNT x z) = gammaSq z / omegaNT x z^2 +
        2 * (x ⬝ᵥ z) + omegaNT x z^2 * gammaSq x := by
      rw [gs_tail]
      simp only [xiNT, Fin.succ_ne_zero, if_false, if_true]
      rw [hsum, gs_tail x, gs_tail z]
      simp only [dotProduct, Fin.sum_univ_succ]
      field_simp
      <;> ring
    rw [hcalc]
    exact add_pos (add_pos (div_pos hz.2 (sq_pos_of_pos hw)) (mul_pos (by norm_num) hdot))
      (mul_pos (sq_pos_of_pos hw) hx.2)

private theorem t_facts {k : ℕ} (x z : Fin (k+1) → ℝ) (hx : socInt x) (hz : socInt z) :
    socInt (tNT x z) ∧ gammaSq (tNT x z) = 1 ∧ gam (tNT x z) = 1 := by
  have hxi := xi_interior x z hx hz
  have hg : 0 < gam (xiNT x z) := Real.sqrt_pos.2 hxi.2
  have hg2 : gam (xiNT x z)^2 = gammaSq (xiNT x z) := Real.sq_sqrt hxi.2.le
  have ht0 : 0 < tNT x z 0 := mul_pos (inv_pos.2 hg) hxi.1
  have hts : gammaSq (tNT x z) = 1 := by
    simp only [tNT, gammaSq, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change (gam (xiNT x z))⁻¹ * ((gam (xiNT x z))⁻¹ * gammaSq (xiNT x z)) = 1
    rw [← hg2]
    field_simp
  refine ⟨⟨ht0, by rw [hts]; norm_num⟩, hts, ?_⟩
  simp [gam, hts]

private theorem boost_square {k : ℕ} (t : Fin (k+1) → ℝ) (ht : socInt t)
    (hs : gammaSq t = 1) : GHKM t * GHKM t = J k + (2 : ℝ) • vecMulVec t t := by
  have hg : gam t = 1 := by simp [gam, hs]
  have hd : 1 + t 0 ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hh : ∑ r : Fin k, t r.succ^2 = t 0^2 - 1 := by rw [gs_tail] at hs; linarith
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  all_goals simp [GHKM, hg, SDPT3.ScaleInv.J, Jbar, diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _),
    Matrix.smul_apply, vecMulVec_apply, add_mul, mul_add, ite_mul, mul_ite,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp only [← pow_two, hh]
    ring
  · simp only [mul_div_assoc, ← mul_assoc, ← pow_two, ← Finset.sum_mul, hh]
    field_simp
    ring
  · simp only [div_mul_eq_mul_div, mul_assoc, ← pow_two, ← Finset.mul_sum, ← Finset.sum_div, hh]
    field_simp
    ring
  · have hsum : (∑ r : Fin k, t i.succ * t r.succ / (1+t 0) *
        (t r.succ * t j.succ / (1+t 0))) =
        t i.succ * t j.succ / (1+t 0)^2 * ∑ r : Fin k, t r.succ^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      field_simp
      <;> ring
    rw [hsum, hh]
    split_ifs <;> field_simp <;> ring

private theorem xi_balance {k : ℕ} (x z : Fin (k+1) → ℝ) (hx : socInt x) (hz : socInt z) :
    gammaSq (xiNT x z) = 2 * omegaNT x z * (xiNT x z ⬝ᵥ x) := by
  have hgx : 0 < gam x := Real.sqrt_pos.2 hx.2
  have hgz : 0 < gam z := Real.sqrt_pos.2 hz.2
  have hw : 0 < omegaNT x z := Real.sqrt_pos.2 (div_pos hgz hgx)
  have hw2 : omegaNT x z^2 = gam z / gam x := Real.sq_sqrt (div_pos hgz hgx).le
  have hs : gammaSq z = (omegaNT x z^2)^2 * gammaSq x := by
    rw [hw2, ← Real.sq_sqrt hz.2.le, ← Real.sq_sqrt hx.2.le]
    field_simp
    simp only [gam]
  have hsum : (∑ i : Fin k, (z i.succ / omegaNT x z - omegaNT x z * x i.succ)^2) =
      (∑ i : Fin k, z i.succ^2) / omegaNT x z ^ 2 -
      2 * (∑ i : Fin k, x i.succ * z i.succ) + omegaNT x z ^ 2 * (∑ i : Fin k, x i.succ^2) := by
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
    <;> ring
  have hdot : xiNT x z ⬝ᵥ x = (x ⬝ᵥ z) / omegaNT x z + omegaNT x z * gammaSq x := by
    simp only [xiNT, dotProduct, Fin.sum_univ_succ, Fin.succ_ne_zero, if_false, if_true,
      sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc, Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.mul_sum, gs_tail, mul_comm]
    ring_nf
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib, mul_assoc]
    try simp only [← Finset.mul_sum]
    ring
  rw [hdot, gs_tail]
  simp only [xiNT, Fin.succ_ne_zero, if_false, if_true]
  rw [hsum]
  have hs' := hs
  rw [gs_tail x, gs_tail z] at hs'
  simp only [dotProduct, Fin.sum_univ_succ, gs_tail]
  field_simp
  nlinarith [hs']

private theorem nt_boost {k : ℕ} (x z : Fin (k+1) → ℝ) (hx : socInt x) (hz : socInt z) :
    GNT x z = omegaNT x z • GHKM (tNT x z) := by
  have hg := (t_facts x z hx hz).2.2
  ext a b
  simp [GNT, GHKM, hg, add_comm]

private theorem nt_square_x {k : ℕ} (x z : Fin (k+1) → ℝ) (hx : socInt x) (hz : socInt z) :
    (GNT x z * GNT x z) *ᵥ x = z := by
  obtain ⟨ht, hs, hg⟩ := t_facts x z hx hz
  have hxi := xi_interior x z hx hz
  have hgxi : gam (xiNT x z)^2 = gammaSq (xiNT x z) := Real.sq_sqrt hxi.2.le
  have hgp : 0 < gam (xiNT x z) := Real.sqrt_pos.2 hxi.2
  have hw : 0 < omegaNT x z := Real.sqrt_pos.2 (div_pos (Real.sqrt_pos.2 hz.2) (Real.sqrt_pos.2 hx.2))
  have hb := xi_balance x z hx hz
  have hc : omegaNT x z^2 * 2 * (gam (xiNT x z))⁻¹ *
      (gam (xiNT x z))⁻¹ * (xiNT x z ⬝ᵥ x) = omegaNT x z := by
    field_simp
    nlinarith [congrArg (fun a : ℝ => a * omegaNT x z) hb]
  rw [nt_boost x z hx hz, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    boost_square _ ht hs]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_add, tNT, smul_dotProduct, smul_eq_mul, smul_smul]
  ext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, SDPT3.ScaleInv.J, Matrix.neg_mulVec,
    Jbar, mulVec_diagonal, Pi.neg_apply]
  calc
    _ = -(omegaNT x z^2 * (if a = 0 then 1 else -1) * x a) +
        omegaNT x z * xiNT x z a := by
      linear_combination (xiNT x z a) * hc
    _ = z a := by
      by_cases ha : a = 0 <;> simp [xiNT, ha] <;> field_simp <;> ring

private theorem jb_sq (k : ℕ) : Jbar k * Jbar k = 1 := by
  simp only [Jbar, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = 0 <;> simp [h, diagonal_apply, Matrix.one_apply]

private theorem arrow_unit {k : ℕ} (v : Fin (k+1) → ℝ) (hv : socInt v) : IsUnit (arw v).det := by
  have hker : ∀ y, arw v *ᵥ y = 0 → y = 0 := by
    intro y hy
    have h0 := congrFun hy 0
    have hi (i : Fin k) := congrFun hy i.succ
    simp [arw, mulVec, dotProduct, Fin.sum_univ_succ] at h0
    simp [arw, mulVec, dotProduct, Fin.sum_univ_succ, mul_ite,
      Finset.sum_ite_eq'] at hi
    have hh : (∑ i : Fin k, v i.succ^2) * y 0 + v 0 * (∑ i : Fin k, v i.succ*y i.succ) = 0 := by
      have hh' : ∑ i : Fin k, v i.succ * (v i.succ*y 0 + v 0*y i.succ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi'
        rw [hi i, mul_zero]
      simp only [mul_add, ← mul_assoc, ← pow_two, Finset.sum_add_distrib, ← Finset.sum_mul] at hh'
      convert hh' using 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      ring
    have hy0 : y 0 = 0 := by
      have hh0 : gammaSq v * y 0 = 0 := by
        rw [gs_tail]
        linear_combination v 0 * h0 - hh
      exact (mul_eq_zero.mp hh0).resolve_left hv.2.ne'
    ext a
    refine Fin.cases hy0 (fun i => ?_) a
    have h := hi i
    simp only [hy0, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hv.1.ne'
  apply (isUnit_iff_isUnit_det _).mp
  apply mulVec_injective_iff_isUnit.mp
  intro y y' hh
  have h := hker (y-y') (by rw [Matrix.mulVec_sub, hh, sub_self])
  exact sub_eq_zero.mp h

theorem solution {k : ℕ} (x z : Fin (k + 1) → ℝ) (hx : socInt x) (hz : socInt z) :
    IsUnit (GNT x z).det ∧ GNT x z *ᵥ x = (GNT x z)⁻¹ *ᵥ z ∧
      (calE (GNT x z) z)⁻¹ * calF (GNT x z) x = (GNT x z)⁻¹ * (GNT x z)⁻¹ ∧
      (GNT x z)⁻¹ * (GNT x z)⁻¹ =
        (omegaNT x z ^ 2)⁻¹ • (J k + (2 : ℝ) • vecMulVec (Jbar k *ᵥ tNT x z) (Jbar k *ᵥ tNT x z)) := by
  obtain ⟨ht, hs, hg⟩ := t_facts x z hx hz
  obtain ⟨huB, _, _⟩ := hkm (tNT x z) ht
  have hw : 0 < omegaNT x z := Real.sqrt_pos.2 (div_pos (Real.sqrt_pos.2 hz.2) (Real.sqrt_pos.2 hx.2))
  have hleft : (omegaNT x z)⁻¹ • (GHKM (tNT x z))⁻¹ * GNT x z = 1 := by
    rw [nt_boost x z hx hz]
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, nonsing_inv_mul _ huB, hw.ne']
  have huG := isUnit_det_of_left_inverse hleft
  have hGx : GNT x z *ᵥ x = (GNT x z)⁻¹ *ᵥ z := by
    have h := congrArg (fun v => (GNT x z)⁻¹ *ᵥ v) (nt_square_x x z hx hz)
    simpa only [mulVec_mulVec, ← mul_assoc, nonsing_inv_mul _ huG, one_mul] using h
  refine ⟨huG, hGx, ?_, ?_⟩
  · have hsym : (GHKM (tNT x z))ᵀ = GHKM (tNT x z) := by
      ext a b
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
        simp [GHKM, transpose_apply, ha, hb, mul_comm, eq_comm]
    have hgsym : (GNT x z)ᵀ = GNT x z := by
      rw [nt_boost x z hx hz, transpose_smul, hsym]
    have hmetric : (GNT x z)ᵀ * Jbar k * GNT x z = omegaNT x z^2 • Jbar k := by
      rw [hgsym, nt_boost x z hx hz]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [metric_hkm _ ht, hs, one_smul, pow_two]
    have hv : socInt (GNT x z *ᵥ x) := by
      constructor
      · have hp := dot_pos (tNT x z) x ht hx
        have he : (GNT x z *ᵥ x) 0 = omegaNT x z * (tNT x z ⬝ᵥ x) := by
          rw [nt_boost x z hx hz]
          simp [GHKM, mulVec, dotProduct, Matrix.smul_apply, Finset.mul_sum, mul_assoc]
        rw [he]
        exact mul_pos hw hp
      · have he : gammaSq (GNT x z *ᵥ x) = omegaNT x z^2 * gammaSq x := by
          rw [gammaSq, dotProduct_comm, ← dotProduct_transpose_mulVec]
          rw [mulVec_mulVec, mulVec_mulVec, hmetric, Matrix.smul_mulVec, dotProduct_smul]
          rfl
        rw [he]
        exact mul_pos (sq_pos_of_pos hw) hx.2
    have ha := arrow_unit (GNT x z *ᵥ x) hv
    rw [calE, calF, ← hGx, Matrix.mul_inv_rev]
    rw [mul_assoc, nonsing_inv_mul_cancel_left _ _ ha]
  · have hiG := inv_eq_left_inv hleft
    have hm : GHKM (tNT x z) * Jbar k * GHKM (tNT x z) = Jbar k := by
      rw [metric_hkm _ ht, hs, one_smul]
    have hiB : (GHKM (tNT x z))⁻¹ = Jbar k * GHKM (tNT x z) * Jbar k := by
      apply inv_eq_left_inv
      calc
        _ = Jbar k * (GHKM (tNT x z) * Jbar k * GHKM (tNT x z)) := by simp only [mul_assoc]
        _ = 1 := by rw [hm, jb_sq]
    rw [hiG, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hiB]
    have hh : (Jbar k * GHKM (tNT x z) * Jbar k) * (Jbar k * GHKM (tNT x z) * Jbar k) =
        Jbar k * (GHKM (tNT x z) * GHKM (tNT x z)) * Jbar k := by
      simp only [mul_assoc, ← mul_assoc (Jbar k) (Jbar k), jb_sq, one_mul]
    rw [hh, boost_square _ ht hs]
    have hjt : (Jbar k)ᵀ = Jbar k := by simp [Jbar]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      SDPT3.ScaleInv.J, mul_neg, neg_mul, mul_assoc, jb_sq, mul_one, one_mul,
      mul_vecMulVec, vecMulVec_mul, ← mulVec_transpose, hjt]
    congr 1
    field_simp

#print axioms solution
