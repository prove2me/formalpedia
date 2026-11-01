-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.certifiedSDPBounds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T11:12:31.355382+00:00
-- url     : https://prove2.me/submissions/aeff51f6-617a-4656-bf32-292eea3f9e84

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_cgpCompactAttainment
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_concreteCGPNonempty

open scoped ComplexConjugate ComplexOrder Matrix BigOperators

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

attribute [local instance] Classical.propDecidable

lemma fE0 : fixedEnergy 0 = 0 := rfl
lemma fE1 : fixedEnergy 1 = 1 := rfl
lemma fE2 : fixedEnergy 2 = 1 := rfl
lemma fE3 : fixedEnergy 3 = 3 := rfl

def a : ℝ := Real.exp (-1)
def a_lo : ℝ := 3678794411 / 10000000000
def a_hi : ℝ := 3678794413 / 10000000000
def a3_lo : ℝ := 497870683 / 10000000000
def a3_hi : ℝ := 497870685 / 10000000000

lemma a_bounds : a_lo < a ∧ a < a_hi := by
  have h1 := Real.exp_neg_one_gt_d9
  have h2 := Real.exp_neg_one_lt_d9
  unfold a a_lo a_hi
  constructor <;> linarith

lemma a3_bounds : a3_lo < a ^ 3 ∧ a ^ 3 < a3_hi := by
  obtain ⟨hlo, hhi⟩ := a_bounds
  have h1 : 0 ≤ a_lo := by unfold a_lo; norm_num
  have h2 : a3_lo < a_lo ^ 3 := by unfold a3_lo a_lo; norm_num
  have h3 : a_hi ^ 3 < a3_hi := by unfold a3_hi a_hi; norm_num
  constructor
  · have hpow : a_lo ^ 3 < a ^ 3 := @pow_lt_pow_left₀ ℝ _ _ _ _ _ _ hlo h1 3 (by decide)
    exact lt_trans h2 hpow
  · have hpow : a ^ 3 < a_hi ^ 3 := @pow_lt_pow_left₀ ℝ _ _ _ _ _ _ hhi (by linarith) 3 (by decide)
    exact lt_trans hpow h3

def G : Fin 4 → ℝ
  | 0 => 1
  | 1 => a
  | 2 => a
  | 3 => a ^ 3

lemma exp_fixedEnergy (u : Fin 4) : Real.exp (-1 * fixedEnergy u) = G u := by
  fin_cases u <;> simp [fixedEnergy, G, a]
  rw [← Real.exp_nat_mul]; norm_num

lemma G_sum_pos : 0 < ∑ j, G j := by
  have ha : 0 < a := by
    have := a_bounds.1
    have : 0 < a_lo := by unfold a_lo; norm_num
    linarith
  have ha3 : 0 < a ^ 3 := by
    have := a3_bounds.1
    have : 0 < a3_lo := by unfold a3_lo; norm_num
    linarith
  simp only [Fin.sum_univ_four, G]
  linarith

lemma gibbsWeight_eq (u : Fin 4) :
    gibbsWeight fixedEnergy 1 u = G u / ∑ j, G j := by
  unfold gibbsWeight
  simp_rw [exp_fixedEnergy]

lemma g52c_psd_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (r s : ι) :
    ‖M r s‖ ^ 2 ≤ (M r r).re * (M s s).re := by
  have h2 := (hM.submatrix ![r, s]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  have hsr : M s r = star (M r s) := (hM.1.apply s r).symm
  have hrr : (M r r).im = 0 := by
    have := hM.1.apply r r
    have h3 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h3
    linarith
  have hss : (M s s).im = 0 := by
    have := hM.1.apply s s
    have h3 := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at h3
    linarith
  rw [hsr] at h2
  have h4 := (Complex.nonneg_iff.mp h2).1
  simp only [Complex.sub_re, Complex.mul_re, hrr, hss, mul_zero, sub_zero, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at h4
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith [h4]

lemma re_sq_le_norm_sq (z : ℂ) : (z.re) ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have : 0 ≤ z.im ^ 2 := sq_nonneg z.im
  linarith

lemma psd_entry_re_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℝ) (h_sq : r ^ 2 ≤ x * y)
    (c : ℝ) (hc : 0 < c) :
    r ≤ (1 / 2 : ℝ) * (c * x + c⁻¹ * y) := by
  by_cases hr : r ≤ 0
  · have : 0 ≤ (1 / 2 : ℝ) * (c * x + c⁻¹ * y) := by
      have : 0 ≤ c * x := mul_nonneg hc.le hx
      have : 0 ≤ c⁻¹ * y := mul_nonneg (inv_pos.mpr hc).le hy
      linarith
    linarith
  · push Not at hr
    have h_diff : 0 ≤ (c * x - c⁻¹ * y) ^ 2 := sq_nonneg _
    have h_inv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
    have h_sq_bound : (2 * r) ^ 2 ≤ (c * x + c⁻¹ * y) ^ 2 := by
      calc (2 * r) ^ 2 = 4 * r ^ 2 := by ring
      _ ≤ 4 * (x * y) := by nlinarith
      _ = 4 * (c * c⁻¹) * (x * y) := by rw [h_inv, mul_one]
      _ = 4 * (c * x) * (c⁻¹ * y) := by ring
      _ ≤ (c * x + c⁻¹ * y) ^ 2 := by nlinarith [h_diff]
    have h_pos_lhs : 0 ≤ 2 * r := by linarith
    have h_pos_rhs : 0 ≤ c * x + c⁻¹ * y := by
      have : 0 ≤ c * x := mul_nonneg hc.le hx
      have : 0 ≤ c⁻¹ * y := mul_nonneg (inv_pos.mpr hc).le hy
      linarith
    have h_le := (sq_le_sq.mp h_sq_bound)
    rw [abs_of_nonneg h_pos_lhs, abs_of_nonneg h_pos_rhs] at h_le
    linarith

lemma fixedRho_00 : fixedRho 0 0 = (35/100 : ℂ) := rfl
lemma fixedRho_01 : fixedRho 0 1 = (5/100 : ℂ) := rfl
lemma fixedRho_02 : fixedRho 0 2 = (0 : ℂ) := rfl
lemma fixedRho_03 : fixedRho 0 3 = (4/100 : ℂ) := rfl
lemma fixedRho_10 : fixedRho 1 0 = (5/100 : ℂ) := rfl
lemma fixedRho_11 : fixedRho 1 1 = (25/100 : ℂ) := rfl
lemma fixedRho_12 : fixedRho 1 2 = (0 : ℂ) := rfl
lemma fixedRho_13 : fixedRho 1 3 = (0 : ℂ) := rfl
lemma fixedRho_20 : fixedRho 2 0 = (0 : ℂ) := rfl
lemma fixedRho_21 : fixedRho 2 1 = (0 : ℂ) := rfl
lemma fixedRho_22 : fixedRho 2 2 = (20/100 : ℂ) := rfl
lemma fixedRho_23 : fixedRho 2 3 = (5/100 : ℂ) := rfl
lemma fixedRho_30 : fixedRho 3 0 = (4/100 : ℂ) := rfl
lemma fixedRho_31 : fixedRho 3 1 = (0 : ℂ) := rfl
lemma fixedRho_32 : fixedRho 3 2 = (5/100 : ℂ) := rfl
lemma fixedRho_33 : fixedRho 3 3 = (20/100 : ℂ) := rfl

lemma objPair0 : objectivePair 0 = (0, 1) := rfl
lemma objPair1 : objectivePair 1 = (2, 3) := rfl
lemma objPair2 : objectivePair 2 = (0, 3) := rfl

lemma channelObjective_0_eq (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (h_cov : ∀ x u y v, fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v → J (x, u) (y, v) = 0) :
    channelObjective 0 (fromChoi J) = (1 / 20 : ℝ) * (J (0, 0) (1, 1)).re := by
  unfold channelObjective fromChoi
  rw [objPair0]
  simp only [Fin.sum_univ_four,
    fixedRho_00, fixedRho_01, fixedRho_02, fixedRho_03,
    fixedRho_10, fixedRho_11, fixedRho_12, fixedRho_13,
    fixedRho_20, fixedRho_21, fixedRho_22, fixedRho_23,
    fixedRho_30, fixedRho_31, fixedRho_32, fixedRho_33,
    mul_zero, add_zero, zero_add]
  have z_00 : J (0, 0) (1, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_03 : J (0, 0) (1, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_10 : J (0, 1) (1, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_11 : J (0, 1) (1, 1) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_22 : J (0, 2) (1, 2) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_23 : J (0, 2) (1, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_30 : J (0, 3) (1, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_32 : J (0, 3) (1, 2) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_33 : J (0, 3) (1, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  rw [z_00, z_03, z_10, z_11, z_22, z_23, z_30, z_32, z_33]
  simp only [zero_mul, add_zero, zero_add]
  have : (5 / 100 : ℂ) = ((1 / 20 : ℝ) : ℂ) := by norm_num
  rw [this, mul_comm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma channelObjective_1_eq (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (h_cov : ∀ x u y v, fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v → J (x, u) (y, v) = 0) :
    channelObjective 1 (fromChoi J) = (1 / 20 : ℝ) * (J (2, 2) (3, 3)).re := by
  unfold channelObjective fromChoi
  rw [objPair1]
  simp only [Fin.sum_univ_four,
    fixedRho_00, fixedRho_01, fixedRho_02, fixedRho_03,
    fixedRho_10, fixedRho_11, fixedRho_12, fixedRho_13,
    fixedRho_20, fixedRho_21, fixedRho_22, fixedRho_23,
    fixedRho_30, fixedRho_31, fixedRho_32, fixedRho_33,
    mul_zero, add_zero, zero_add]
  have z_00 : J (2, 0) (3, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_01 : J (2, 0) (3, 1) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_03 : J (2, 0) (3, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_10 : J (2, 1) (3, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_11 : J (2, 1) (3, 1) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_22 : J (2, 2) (3, 2) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_30 : J (2, 3) (3, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_32 : J (2, 3) (3, 2) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_33 : J (2, 3) (3, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  rw [z_00, z_01, z_03, z_10, z_11, z_22, z_30, z_32, z_33]
  simp only [zero_mul, add_zero, zero_add]
  have : (5 / 100 : ℂ) = ((1 / 20 : ℝ) : ℂ) := by norm_num
  rw [this, mul_comm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma channelObjective_2_eq (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (h_cov : ∀ x u y v, fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v → J (x, u) (y, v) = 0) :
    channelObjective 2 (fromChoi J) = (1 / 25 : ℝ) * (J (0, 0) (3, 3)).re := by
  unfold channelObjective fromChoi
  rw [objPair2]
  simp only [Fin.sum_univ_four,
    fixedRho_00, fixedRho_01, fixedRho_02, fixedRho_03,
    fixedRho_10, fixedRho_11, fixedRho_12, fixedRho_13,
    fixedRho_20, fixedRho_21, fixedRho_22, fixedRho_23,
    fixedRho_30, fixedRho_31, fixedRho_32, fixedRho_33,
    mul_zero, add_zero, zero_add]
  have z_00 : J (0, 0) (3, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_01 : J (0, 0) (3, 1) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_10 : J (0, 1) (3, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_11 : J (0, 1) (3, 1) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_22 : J (0, 2) (3, 2) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_23 : J (0, 2) (3, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_30 : J (0, 3) (3, 0) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_32 : J (0, 3) (3, 2) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  have z_33 : J (0, 3) (3, 3) = 0 := by apply h_cov; norm_num [fE0, fE1, fE2, fE3]
  rw [z_00, z_01, z_10, z_11, z_22, z_23, z_30, z_32, z_33]
  simp only [zero_mul, add_zero, zero_add]
  have : (4 / 100 : ℂ) = ((1 / 25 : ℝ) : ℂ) := by norm_num
  rw [this, mul_comm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma fixedEnergy_diff_ne {i : Fin 4} {u v : Fin 4} (h : fixedEnergy u ≠ fixedEnergy v) :
    fixedEnergy i - fixedEnergy u ≠ fixedEnergy i - fixedEnergy v := fun h_eq => h (by linarith)

lemma fromChoi_fixedRho_diag (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (h_cov : ∀ x u y v, fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v → J (x, u) (y, v) = 0)
    (i : Fin 4) :
    fromChoi J fixedRho i i =
      (35/100 : ℂ) * J (i, 0) (i, 0) +
      (25/100 : ℂ) * J (i, 1) (i, 1) +
      (20/100 : ℂ) * J (i, 2) (i, 2) +
      (20/100 : ℂ) * J (i, 3) (i, 3) := by
  unfold fromChoi
  simp only [Fin.sum_univ_four,
    fixedRho_00, fixedRho_01, fixedRho_02, fixedRho_03,
    fixedRho_10, fixedRho_11, fixedRho_12, fixedRho_13,
    fixedRho_20, fixedRho_21, fixedRho_22, fixedRho_23,
    fixedRho_30, fixedRho_31, fixedRho_32, fixedRho_33,
    mul_zero, add_zero, zero_add]
  have z01 : J (i, 0) (i, 1) = 0 := h_cov _ _ _ _ (fixedEnergy_diff_ne (by norm_num [fE0, fE1, fE2, fE3]))
  have z03 : J (i, 0) (i, 3) = 0 := h_cov _ _ _ _ (fixedEnergy_diff_ne (by norm_num [fE0, fE1, fE2, fE3]))
  have z10 : J (i, 1) (i, 0) = 0 := h_cov _ _ _ _ (fixedEnergy_diff_ne (by norm_num [fE0, fE1, fE2, fE3]))
  have z23 : J (i, 2) (i, 3) = 0 := h_cov _ _ _ _ (fixedEnergy_diff_ne (by norm_num [fE0, fE1, fE2, fE3]))
  have z30 : J (i, 3) (i, 0) = 0 := h_cov _ _ _ _ (fixedEnergy_diff_ne (by norm_num [fE0, fE1, fE2, fE3]))
  have z32 : J (i, 3) (i, 2) = 0 := h_cov _ _ _ _ (fixedEnergy_diff_ne (by norm_num [fE0, fE1, fE2, fE3]))
  rw [z01, z03, z10, z23, z30, z32]
  ring

/-! ### Step 2: Upper Bound Certificate via Dual Linear Programming -/

def c0 : ℝ := 92 / 169
def c1 : ℝ := 5195 / 5964
def c2 : ℝ := 1170994349 / 1130200000

lemma c0_pos : 0 < c0 := by unfold c0; norm_num
lemma c1_pos : 0 < c1 := by unfold c1; norm_num
lemma c2_pos : 0 < c2 := by unfold c2; norm_num

def A0 : ℝ := 327871044981 / 9550190000000
def A1 : ℝ := 169 / 3680
def A2 : ℝ := 1039 / 47712
def A3 : ℝ := 2920230374359 / 60833156430550

lemma dual_lp_bound (T : Fin 4 → Fin 4 → ℝ)
    (h_col1 : T 0 1 + T 1 1 + T 2 1 + T 3 1 = 1)
    (h_col2 : T 0 2 + T 1 2 + T 2 2 + T 3 2 = 1)
    (h_col3 : T 0 3 + T 1 3 + T 2 3 + T 3 3 = 1)
    (h_G0_lo : T 0 0 + a_lo * T 0 1 + a_lo * T 0 2 + a3_lo * T 0 3 ≤ 1)
    (h_G3_lo : T 3 0 + a_lo * T 3 1 + a_lo * T 3 2 + a3_lo * T 3 3 ≤ a3_hi)
    (h_R0 : 7 * T 0 0 + 5 * T 0 1 + 4 * T 0 2 + 4 * T 0 3 = 10)
    (h_R3 : 7 * T 3 0 + 5 * T 3 1 + 4 * T 3 2 + 4 * T 3 3 = 3)
    (hT21 : 0 ≤ T 2 1) (hT31 : 0 ≤ T 3 1)
    (hT12 : 0 ≤ T 1 2) (hT22 : 0 ≤ T 2 2) (hT32 : 0 ≤ T 3 2)
    (hT13 : 0 ≤ T 1 3) (hT23 : 0 ≤ T 2 3) :
    A0 * T 0 0 + A1 * T 1 1 + A2 * T 2 2 + A3 * T 3 3 ≤ (881264 / 10000000 : ℝ) := by
  dsimp [A0, A1, A2, A3, a_lo, a_hi, a3_lo, a3_hi] at *
  linarith only [h_col1, h_col2, h_col3, h_G0_lo, h_G3_lo, h_R0, h_R3,
    hT21, hT31, hT12, hT22, hT32, hT13, hT23]

lemma upper_bound_on_feasible (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hJ : FixedChoiFeasible J) :
    ∑ k : Fin 3, channelObjective k (fromChoi J) ≤ (881264 / 10000000 : ℝ) := by
  let T (x u : Fin 4) : ℝ := (J (x, u) (x, u)).re
  have hT_nonneg : ∀ x u, 0 ≤ T x u := fun x u => (Complex.nonneg_iff.mp (hJ.1.diag_nonneg (i := (x, u)))).1

  have h_sq0 : ((J (0, 0) (1, 1)).re) ^ 2 ≤ T 0 0 * T 1 1 := by
    have h_le := g52c_psd_entry J hJ.1 (0, 0) (1, 1)
    have h_re := re_sq_le_norm_sq (J (0, 0) (1, 1))
    linarith
  have h_sq1 : ((J (2, 2) (3, 3)).re) ^ 2 ≤ T 2 2 * T 3 3 := by
    have h_le := g52c_psd_entry J hJ.1 (2, 2) (3, 3)
    have h_re := re_sq_le_norm_sq (J (2, 2) (3, 3))
    linarith
  have h_sq2 : ((J (0, 0) (3, 3)).re) ^ 2 ≤ T 0 0 * T 3 3 := by
    have h_le := g52c_psd_entry J hJ.1 (0, 0) (3, 3)
    have h_re := re_sq_le_norm_sq (J (0, 0) (3, 3))
    linarith

  have h_obj0 : channelObjective 0 (fromChoi J) ≤ (1 / 40 : ℝ) * (c0 * T 0 0 + c0⁻¹ * T 1 1) := by
    rw [channelObjective_0_eq J hJ.2.2.2.1]
    have := psd_entry_re_le (T 0 0) (T 1 1) (hT_nonneg 0 0) (hT_nonneg 1 1) _ h_sq0 c0 c0_pos
    linarith
  have h_obj1 : channelObjective 1 (fromChoi J) ≤ (1 / 40 : ℝ) * (c1 * T 2 2 + c1⁻¹ * T 3 3) := by
    rw [channelObjective_1_eq J hJ.2.2.2.1]
    have := psd_entry_re_le (T 2 2) (T 3 3) (hT_nonneg 2 2) (hT_nonneg 3 3) _ h_sq1 c1 c1_pos
    linarith
  have h_obj2 : channelObjective 2 (fromChoi J) ≤ (1 / 50 : ℝ) * (c2 * T 0 0 + c2⁻¹ * T 3 3) := by
    rw [channelObjective_2_eq J hJ.2.2.2.1]
    have := psd_entry_re_le (T 0 0) (T 3 3) (hT_nonneg 0 0) (hT_nonneg 3 3) _ h_sq2 c2 c2_pos
    linarith

  have h_sum_le : ∑ k : Fin 3, channelObjective k (fromChoi J) ≤
      A0 * T 0 0 + A1 * T 1 1 + A2 * T 2 2 + A3 * T 3 3 := by
    simp only [Fin.sum_univ_three]
    have : (1 / 40 : ℝ) * (c0 * T 0 0 + c0⁻¹ * T 1 1) +
           (1 / 40 : ℝ) * (c1 * T 2 2 + c1⁻¹ * T 3 3) +
           (1 / 50 : ℝ) * (c2 * T 0 0 + c2⁻¹ * T 3 3) =
           A0 * T 0 0 + A1 * T 1 1 + A2 * T 2 2 + A3 * T 3 3 := by
      dsimp [A0, A1, A2, A3, c0, c1, c2]; ring
    linarith

  have h_col1 : T 0 1 + T 1 1 + T 2 1 + T 3 1 = 1 := by
    have h := hJ.2.1 1 1
    rw [if_pos rfl] at h
    have h_re := congrArg Complex.re h
    simp only [Fin.sum_univ_four, Complex.add_re, Complex.one_re] at h_re
    exact h_re
  have h_col2 : T 0 2 + T 1 2 + T 2 2 + T 3 2 = 1 := by
    have h := hJ.2.1 2 2
    rw [if_pos rfl] at h
    have h_re := congrArg Complex.re h
    simp only [Fin.sum_univ_four, Complex.add_re, Complex.one_re] at h_re
    exact h_re
  have h_col3 : T 0 3 + T 1 3 + T 2 3 + T 3 3 = 1 := by
    have h := hJ.2.1 3 3
    rw [if_pos rfl] at h
    have h_re := congrArg Complex.re h
    simp only [Fin.sum_univ_four, Complex.add_re, Complex.one_re] at h_re
    exact h_re

  have h_G0 : T 0 0 + a * T 0 1 + a * T 0 2 + a ^ 3 * T 0 3 = 1 := by
    have h := hJ.2.2.1 0 0
    rw [if_pos rfl] at h
    have h_re := congrArg Complex.re h
    simp only [Fin.sum_univ_four, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at h_re
    change T 0 0 * gibbsWeight fixedEnergy 1 0 +
           T 0 1 * gibbsWeight fixedEnergy 1 1 +
           T 0 2 * gibbsWeight fixedEnergy 1 2 +
           T 0 3 * gibbsWeight fixedEnergy 1 3 = gibbsWeight fixedEnergy 1 0 at h_re
    simp_rw [gibbsWeight_eq] at h_re
    have h_div : T 0 0 * (G 0 / ∑ j, G j) +
                 T 0 1 * (G 1 / ∑ j, G j) +
                 T 0 2 * (G 2 / ∑ j, G j) +
                 T 0 3 * (G 3 / ∑ j, G j) =
                 (T 0 0 * G 0 + T 0 1 * G 1 + T 0 2 * G 2 + T 0 3 * G 3) / ∑ j, G j := by
      ring
    rw [h_div] at h_re
    have h_mul := congrArg (fun r => r * ∑ j, G j) h_re
    rw [div_mul_cancel₀ _ G_sum_pos.ne'] at h_mul
    rw [div_mul_cancel₀ _ G_sum_pos.ne'] at h_mul
    dsimp [G] at h_mul
    linarith
  have h_G3 : T 3 0 + a * T 3 1 + a * T 3 2 + a ^ 3 * T 3 3 = a ^ 3 := by
    have h := hJ.2.2.1 3 3
    rw [if_pos rfl] at h
    have h_re := congrArg Complex.re h
    simp only [Fin.sum_univ_four, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at h_re
    change T 3 0 * gibbsWeight fixedEnergy 1 0 +
           T 3 1 * gibbsWeight fixedEnergy 1 1 +
           T 3 2 * gibbsWeight fixedEnergy 1 2 +
           T 3 3 * gibbsWeight fixedEnergy 1 3 = gibbsWeight fixedEnergy 1 3 at h_re
    simp_rw [gibbsWeight_eq] at h_re
    have h_div : T 3 0 * (G 0 / ∑ j, G j) +
                 T 3 1 * (G 1 / ∑ j, G j) +
                 T 3 2 * (G 2 / ∑ j, G j) +
                 T 3 3 * (G 3 / ∑ j, G j) =
                 (T 3 0 * G 0 + T 3 1 * G 1 + T 3 2 * G 2 + T 3 3 * G 3) / ∑ j, G j := by
      ring
    rw [h_div] at h_re
    have h_mul := congrArg (fun r => r * ∑ j, G j) h_re
    rw [div_mul_cancel₀ _ G_sum_pos.ne'] at h_mul
    rw [div_mul_cancel₀ _ G_sum_pos.ne'] at h_mul
    dsimp [G] at h_mul
    linarith

  have h_R0 : 7 * T 0 0 + 5 * T 0 1 + 4 * T 0 2 + 4 * T 0 3 = 10 := by
    have h := hJ.2.2.2.2.1
    rw [fromChoi_fixedRho_diag J hJ.2.2.2.1 0] at h
    have h0 : (35/100 : ℂ) = ((7/20 : ℝ) : ℂ) := by norm_num
    have h1 : (25/100 : ℂ) = ((5/20 : ℝ) : ℂ) := by norm_num
    have h2 : (20/100 : ℂ) = ((4/20 : ℝ) : ℂ) := by norm_num
    have h3 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    rw [h0, h1, h2, h3] at h
    have h_re := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h_re
    dsimp [T]
    linarith

  have h_R3 : 7 * T 3 0 + 5 * T 3 1 + 4 * T 3 2 + 4 * T 3 3 = 3 := by
    have h := hJ.2.2.2.2.2.2
    rw [fromChoi_fixedRho_diag J hJ.2.2.2.1 3] at h
    have h0 : (35/100 : ℂ) = ((7/20 : ℝ) : ℂ) := by norm_num
    have h1 : (25/100 : ℂ) = ((5/20 : ℝ) : ℂ) := by norm_num
    have h2 : (20/100 : ℂ) = ((4/20 : ℝ) : ℂ) := by norm_num
    have h3 : (3/20 : ℂ) = ((3/20 : ℝ) : ℂ) := by norm_num
    rw [h0, h1, h2, h3] at h
    have h_re := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h_re
    dsimp [T]
    linarith

  have ha_lo := a_bounds.1.le
  have ha3_lo := a3_bounds.1.le
  have ha3_hi := a3_bounds.2.le
  have hT01 := hT_nonneg 0 1
  have hT02 := hT_nonneg 0 2
  have hT03 := hT_nonneg 0 3
  have _hT21 := hT_nonneg 2 1
  have _hT31 := hT_nonneg 3 1
  have _hT12 := hT_nonneg 1 2
  have _hT22 := hT_nonneg 2 2
  have _hT32 := hT_nonneg 3 2
  have _hT13 := hT_nonneg 1 3
  have _hT23 := hT_nonneg 2 3
  have _hT33 := hT_nonneg 3 3
  have h_G0_lo : T 0 0 + a_lo * T 0 1 + a_lo * T 0 2 + a3_lo * T 0 3 ≤ 1 := by
    have h1 : a_lo * T 0 1 ≤ a * T 0 1 := mul_le_mul_of_nonneg_right ha_lo hT01
    have h2 : a_lo * T 0 2 ≤ a * T 0 2 := mul_le_mul_of_nonneg_right ha_lo hT02
    have h3 : a3_lo * T 0 3 ≤ a ^ 3 * T 0 3 := mul_le_mul_of_nonneg_right ha3_lo hT03
    linarith [h_G0]
  have h_G3_lo : T 3 0 + a_lo * T 3 1 + a_lo * T 3 2 + a3_lo * T 3 3 ≤ a3_hi := by
    have h1 : a_lo * T 3 1 ≤ a * T 3 1 := mul_le_mul_of_nonneg_right ha_lo _hT31
    have h2 : a_lo * T 3 2 ≤ a * T 3 2 := mul_le_mul_of_nonneg_right ha_lo _hT32
    have h3 : a3_lo * T 3 3 ≤ a ^ 3 * T 3 3 := mul_le_mul_of_nonneg_right ha3_lo _hT33
    linarith [h_G3]
  have h_dual := dual_lp_bound T h_col1 h_col2 h_col3 h_G0_lo h_G3_lo h_R0 h_R3
    _hT21 _hT31 _hT12 _hT22 _hT32 _hT13 _hT23
  exact le_trans h_sum_le h_dual

lemma cgpSumOptimum_le : cgpSumOptimum ≤ (881264 / 10000000 : ℝ) := by
  have hne : ((fun J => ∑ k : Fin 3, channelObjective k (fromChoi J)) '' {J | FixedChoiFeasible J}).Nonempty := by
    obtain ⟨J, hJ⟩ := concreteCGPNonempty.2
    exact ⟨_, Set.mem_image_of_mem _ hJ⟩
  apply csSup_le hne
  rintro _ ⟨J, hJ, rfl⟩
  exact upper_bound_on_feasible J hJ

/-! ### Step 3: Explicit Channel Witnesses and Lower Bounds -/

def M_of (T : Fin 4 → Fin 4 → ℝ) : Matrix (Unit ⊕ (Fin 4 × Fin 4)) (Fin 4 × Fin 4) ℂ
  | Sum.inl (), p => if p.1 = p.2 then ((Real.sqrt (T p.1 p.1) : ℝ) : ℂ) else 0
  | Sum.inr (x, u), p => if x ≠ u ∧ (x, u) = p then ((Real.sqrt (T x u) : ℝ) : ℂ) else 0

def J_of (T : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  (M_of T)ᴴ * (M_of T)

theorem J_of_posSemidef (T : Fin 4 → Fin 4 → ℝ) :
    (J_of T).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

lemma J_of_apply (T : Fin 4 → Fin 4 → ℝ) (p q : Fin 4 × Fin 4) :
    J_of T p q =
      (if p.1 = p.2 ∧ q.1 = q.2 then ((Real.sqrt (T p.1 p.1) * Real.sqrt (T q.1 q.1) : ℝ) : ℂ) else 0) +
      (if p.1 ≠ p.2 ∧ p = q then ((Real.sqrt (T p.1 p.2) * Real.sqrt (T p.1 p.2) : ℝ) : ℂ) else 0) := by
  dsimp [J_of]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  have hunit : ∀ f : Unit → ℂ, ∑ a, f a = f () := fun f => by
    have : (Finset.univ : Finset Unit) = {()} := by decide
    rw [this, Finset.sum_singleton]
  rw [hunit]
  dsimp [M_of]
  have h1 : (starRingEnd ℂ) (if p.1 = p.2 then (Real.sqrt (T p.1 p.1) : ℂ) else 0) *
      (if q.1 = q.2 then (Real.sqrt (T q.1 q.1) : ℂ) else 0) =
      if p.1 = p.2 ∧ q.1 = q.2 then ((Real.sqrt (T p.1 p.1) * Real.sqrt (T q.1 q.1) : ℝ) : ℂ) else 0 := by
    by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq]
  rw [h1]
  congr 1
  by_cases hpq : p.1 ≠ p.2 ∧ p = q
  · rw [if_pos hpq]
    obtain ⟨hp_ne, hpq_eq⟩ := hpq
    rw [Finset.sum_eq_single p]
    · subst hpq_eq
      simp [hp_ne]
    · intro ⟨x, u⟩ _ hne
      have : ¬ (x ≠ u ∧ (x, u) = p) := fun ⟨_, heq⟩ => hne heq
      simp [this]
    · simp
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    intro ⟨x, u⟩ _
    by_cases hx : x ≠ u ∧ (x, u) = p
    · have hne := hx.1
      have heq := hx.2
      have hq_ne : ¬ (x ≠ u ∧ (x, u) = q) := fun ⟨_, heq_q⟩ => by
        have : p = q := heq.symm.trans heq_q
        exact hpq ⟨heq ▸ hne, this⟩
      rw [if_neg hq_ne, mul_zero]
    · rw [if_neg hx]
      simp only [map_zero, zero_mul]

set_option linter.unusedSimpArgs false in
lemma J_of_diag (T : Fin 4 → Fin 4 → ℝ) (hT : ∀ x u, 0 ≤ T x u) (x u : Fin 4) :
    J_of T (x, u) (x, u) = (T x u : ℂ) := by
  rw [J_of_apply]
  by_cases h : x = u
  · subst h
    have h1 : (x, x).1 = (x, x).2 ∧ (x, x).1 = (x, x).2 := ⟨rfl, rfl⟩
    have h2 : ¬ ((x, x).1 ≠ (x, x).2 ∧ (x, x) = (x, x)) := fun ⟨hne, _⟩ => hne rfl
    rw [if_pos h1, if_neg h2, add_zero]
    simp only [Real.mul_self_sqrt (hT x x)]
  · have h1 : ¬ ((x, u).1 = (x, u).2 ∧ (x, u).1 = (x, u).2) := fun ⟨hxu, _⟩ => h hxu
    have h2 : (x, u).1 ≠ (x, u).2 ∧ (x, u) = (x, u) := ⟨h, rfl⟩
    rw [if_neg h1, if_pos h2, zero_add]
    simp only [Real.mul_self_sqrt (hT x u)]

lemma J_of_cov (T : Fin 4 → Fin 4 → ℝ) (x u y v : Fin 4)
    (h : fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v) :
    J_of T (x, u) (y, v) = 0 := by
  rw [J_of_apply]
  have h1 : ¬ ((x, u).1 = (x, u).2 ∧ (y, v).1 = (y, v).2) := fun ⟨hxu, hyv⟩ => by
    dsimp at hxu hyv
    subst hxu hyv
    exact h (by simp)
  have h2 : ¬ ((x, u) = (y, v)) := fun heq => by
    injection heq with hx hu
    subst hx hu
    exact h rfl
  have h3 : ¬ ((x, u).1 ≠ (x, u).2 ∧ (x, u) = (y, v)) := fun ⟨_, heq⟩ => h2 heq
  rw [if_neg h1, if_neg h3, zero_add]

lemma J_of_off (T : Fin 4 → Fin 4 → ℝ) (x y : Fin 4) (h : x ≠ y) :
    ∀ u, J_of T (x, u) (y, u) = 0 := by
  intro u
  rw [J_of_apply]
  have h1 : ¬ ((x, u).1 = (x, u).2 ∧ (y, u).1 = (y, u).2) := fun ⟨hxu, hyu⟩ => by
    dsimp at hxu hyu
    exact h (hxu.trans hyu.symm)
  have h2 : ¬ ((x, u) = (y, u)) := fun heq => h (congrArg Prod.fst heq)
  have h3 : ¬ ((x, u).1 ≠ (x, u).2 ∧ (x, u) = (y, u)) := fun ⟨_, heq⟩ => h2 heq
  rw [if_neg h1, if_neg h3, zero_add]

theorem J_of_feasible (T : Fin 4 → Fin 4 → ℝ) (hT : ∀ x u, 0 ≤ T x u)
    (h_col : ∀ u, ∑ x, T x u = 1)
    (h_gibbs : ∀ x, ∑ u, T x u * gibbsWeight fixedEnergy 1 u = gibbsWeight fixedEnergy 1 x)
    (h_pop0 : (35/100 : ℝ) * T 0 0 + (25/100 : ℝ) * T 0 1 + (20/100 : ℝ) * T 0 2 + (20/100 : ℝ) * T 0 3 = 1/2)
    (h_pop12 : (35/100 : ℝ) * (T 1 0 + T 2 0) + (25/100 : ℝ) * (T 1 1 + T 2 1) + (20/100 : ℝ) * (T 1 2 + T 2 2) + (20/100 : ℝ) * (T 1 3 + T 2 3) = 7/20)
    (h_pop3 : (35/100 : ℝ) * T 3 0 + (25/100 : ℝ) * T 3 1 + (20/100 : ℝ) * T 3 2 + (20/100 : ℝ) * T 3 3 = 3/20) :
    FixedChoiFeasible (J_of T) := by
  refine ⟨J_of_posSemidef T, ?_, ?_, ?_, ?_⟩
  · intro u v
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      simp_rw [J_of_diag T hT]
      rw [← Complex.ofReal_sum, h_col u, Complex.ofReal_one]
    · rw [if_neg huv]
      apply Finset.sum_eq_zero
      intro x _
      rw [J_of_apply]
      have h1 : ¬ ((x, u).1 = (x, u).2 ∧ (x, v).1 = (x, v).2) := fun ⟨hxu, hxv⟩ => by
        dsimp at hxu hxv
        subst hxu hxv
        exact huv rfl
      have h2 : ¬ ((x, u) = (x, v)) := fun heq => huv (congrArg Prod.snd heq)
      have h3 : ¬ ((x, u).1 ≠ (x, u).2 ∧ (x, u) = (x, v)) := fun ⟨_, heq⟩ => h2 heq
      rw [if_neg h1, if_neg h3, zero_add]
  · intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      simp_rw [J_of_diag T hT]
      have : ∑ u, (T x u : ℂ) * (gibbsWeight fixedEnergy 1 u : ℂ) =
          ((∑ u, T x u * gibbsWeight fixedEnergy 1 u : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
      rw [this, h_gibbs x]
    · rw [if_neg hxy]
      simp_rw [J_of_off T x y hxy]
      simp
  · intro x u y v h
    exact J_of_cov T x u y v h
  · dsimp [FixedPopulations]
    simp_rw [fromChoi_fixedRho_diag (J_of T) (J_of_cov T)]
    simp_rw [J_of_diag T hT]
    constructor
    · have : (35/100 : ℂ) * (T 0 0 : ℂ) + (25/100 : ℂ) * (T 0 1 : ℂ) + (20/100 : ℂ) * (T 0 2 : ℂ) + (20/100 : ℂ) * (T 0 3 : ℂ) =
          ((35/100 * T 0 0 + 25/100 * T 0 1 + 20/100 * T 0 2 + 20/100 * T 0 3 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, h_pop0]
      push_cast; rfl
    · constructor
      · have : (35/100 : ℂ) * (T 1 0 : ℂ) + (25/100 : ℂ) * (T 1 1 : ℂ) + (20/100 : ℂ) * (T 1 2 : ℂ) + (20/100 : ℂ) * (T 1 3 : ℂ) +
            ((35/100 : ℂ) * (T 2 0 : ℂ) + (25/100 : ℂ) * (T 2 1 : ℂ) + (20/100 : ℂ) * (T 2 2 : ℂ) + (20/100 : ℂ) * (T 2 3 : ℂ)) =
            (((35/100 : ℝ) * (T 1 0 + T 2 0) + (25/100 : ℝ) * (T 1 1 + T 2 1) + (20/100 : ℝ) * (T 1 2 + T 2 2) + (20/100 : ℝ) * (T 1 3 + T 2 3) : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, h_pop12]
        push_cast; rfl
      · have : (35/100 : ℂ) * (T 3 0 : ℂ) + (25/100 : ℂ) * (T 3 1 : ℂ) + (20/100 : ℂ) * (T 3 2 : ℂ) + (20/100 : ℂ) * (T 3 3 : ℂ) =
            ((35/100 * T 3 0 + 25/100 * T 3 1 + 20/100 * T 3 2 + 20/100 * T 3 3 : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, h_pop3]
        push_cast; rfl

lemma J_of_obj0 (T : Fin 4 → Fin 4 → ℝ) :
    channelObjective 0 (fromChoi (J_of T)) = (1/20 : ℝ) * (Real.sqrt (T 0 0) * Real.sqrt (T 1 1)) := by
  rw [channelObjective_0_eq (J_of T) (J_of_cov T), J_of_apply]
  simp

lemma J_of_obj1 (T : Fin 4 → Fin 4 → ℝ) :
    channelObjective 1 (fromChoi (J_of T)) = (1/20 : ℝ) * (Real.sqrt (T 2 2) * Real.sqrt (T 3 3)) := by
  rw [channelObjective_1_eq (J_of T) (J_of_cov T), J_of_apply]
  simp

lemma J_of_obj2 (T : Fin 4 → Fin 4 → ℝ) :
    channelObjective 2 (fromChoi (J_of T)) = (1/25 : ℝ) * (Real.sqrt (T 0 0) * Real.sqrt (T 3 3)) := by
  rw [channelObjective_2_eq (J_of T) (J_of_cov T), J_of_apply]
  simp

lemma channelObjective_le_cgpOptimum (k : Fin 3) (K : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hK : FixedChoiFeasible K) :
    channelObjective k (fromChoi K) ≤ cgpOptimum k := by
  obtain ⟨h_attain, -⟩ := cgpCompactAttainment.2 concreteCGPNonempty.2
  obtain ⟨J_star, hJ_star, h_max⟩ := h_attain k
  have h_le : channelObjective k (fromChoi K) ≤ channelObjective k (fromChoi J_star) := h_max K hK
  have h_sup : channelObjective k (fromChoi J_star) = cgpOptimum k := by
    dsimp [cgpOptimum]
    apply le_antisymm
    · apply le_csSup
      · exact ⟨channelObjective k (fromChoi J_star), fun _ ⟨J, hJ, heq⟩ => heq ▸ h_max J hJ⟩
      · exact Set.mem_image_of_mem _ hJ_star
    · apply csSup_le
      · exact ⟨_, Set.mem_image_of_mem _ hJ_star⟩
      · rintro _ ⟨J, hJ, rfl⟩
        exact h_max J hJ
  linarith

lemma le_sqrt_mul_sqrt {b x y : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : b ^ 2 ≤ x * y) :
    b ≤ Real.sqrt x * Real.sqrt y := by
  rw [← Real.sqrt_mul hx]
  exact (Real.le_sqrt hb (mul_nonneg hx hy)).mpr h

def b0 : ℝ := 32234472 / 1000000000
def b1 : ℝ := 42606896 / 1000000000
def b2 : ℝ := 28168332 / 1000000000

def F : ℝ := 1089724234 / 10000000000
def M1 : ℝ := 3034252553 / 10000000000
def M2 : ℝ := 136347249 / 10000000000
def K1 : ℝ := 6829400198 / 10000000000
def K2 : ℝ := 7261392315 / 10000000000

def s : ℝ := 1 / (5 - 7 * a)
def t : ℝ := 1 / (4 - 7 * a ^ 3)
def u_par : ℝ := 1 / (4 - 4 * a ^ 2)

lemma den_s_pos : 0 < 5 - 7 * a := by
  have := a_bounds.2
  have : a_hi < 5 / 7 := by unfold a_hi; norm_num
  linarith

lemma den_t_pos : 0 < 4 - 7 * a ^ 3 := by
  have := a3_bounds.2
  have : a3_hi < 4 / 7 := by unfold a3_hi; norm_num
  linarith

lemma den_u_pos : 0 < 4 - 4 * a ^ 2 := by
  have ha_pos : 0 < a := by
    have := a_bounds.1
    have : 0 < a_lo := by unfold a_lo; norm_num
    linarith
  have ha_hi := a_bounds.2
  have : a_hi < 1 := by unfold a_hi; norm_num
  nlinarith

lemma s_mul : s * (5 - 7 * a) = 1 := by
  unfold s
  exact div_mul_cancel₀ 1 den_s_pos.ne'

lemma t_mul : t * (4 - 7 * a ^ 3) = 1 := by
  unfold t
  exact div_mul_cancel₀ 1 den_t_pos.ne'

lemma u_mul : u_par * (4 - 4 * a ^ 2) = 1 := by
  unfold u_par
  exact div_mul_cancel₀ 1 den_u_pos.ne'

lemma s_bounds : (41/100 : ℝ) < s ∧ s < 42/100 := by
  have hd : 0 < 5 - 7 * a := den_s_pos
  have ha_lo := a_bounds.1
  have ha_hi := a_bounds.2
  unfold s
  constructor
  · rw [lt_div_iff₀ hd]; dsimp [a_lo, a_hi] at *; linarith
  · rw [div_lt_iff₀ hd]; dsimp [a_lo, a_hi] at *; linarith

lemma t_bounds : (27/100 : ℝ) < t ∧ t < 28/100 := by
  have hd : 0 < 4 - 7 * a ^ 3 := den_t_pos
  have ha_lo := a3_bounds.1
  have ha_hi := a3_bounds.2
  unfold t
  constructor
  · rw [lt_div_iff₀ hd]; dsimp [a3_lo, a3_hi] at *; linarith
  · rw [div_lt_iff₀ hd]; dsimp [a3_lo, a3_hi] at *; linarith

lemma u_bounds : (28/100 : ℝ) < u_par ∧ u_par < 30/100 := by
  have hd : 0 < 4 - 4 * a ^ 2 := den_u_pos
  have ha_lo := a_bounds.1
  have ha_hi := a_bounds.2
  have ha_pos : 0 < a_lo := by unfold a_lo; norm_num
  unfold u_par
  constructor
  · rw [lt_div_iff₀ hd]; dsimp [a_lo, a_hi] at *; nlinarith
  · rw [div_lt_iff₀ hd]; dsimp [a_lo, a_hi] at *; nlinarith

def T12 : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 1 - 2 * a * s - a ^ 3 * t
  | 0, 1 => 2 * s
  | 0, 2 => 0
  | 0, 3 => t
  | 1, 0 => 2 * a * s
  | 1, 1 => 1 - 2 * s
  | 1, 2 => 0
  | 1, 3 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 1
  | 2, 3 => 0
  | 3, 0 => a ^ 3 * t
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 1 - t

lemma T12_nonneg (x u_idx : Fin 4) : 0 ≤ T12 x u_idx := by
  have ha_lo := a_bounds.1
  have ha_hi := a_bounds.2
  have ha3_lo := a3_bounds.1
  have ha3_hi := a3_bounds.2
  have hs_lo := s_bounds.1
  have hs_hi := s_bounds.2
  have ht_lo := t_bounds.1
  have ht_hi := t_bounds.2
  dsimp [a_lo, a_hi, a3_lo, a3_hi] at *
  fin_cases x <;> fin_cases u_idx <;> { simp only [T12]; nlinarith }

lemma T12_col (u_idx : Fin 4) : ∑ x, T12 x u_idx = 1 := by
  fin_cases u_idx <;> { simp only [Fin.sum_univ_four, T12]; ring }

lemma T12_gibbs_sum (x : Fin 4) : ∑ u_idx, T12 x u_idx * G u_idx = G x := by
  fin_cases x <;> { simp only [Fin.sum_univ_four, T12, G]; ring }

lemma T12_gibbs (x : Fin 4) : ∑ u_idx, T12 x u_idx * gibbsWeight fixedEnergy 1 u_idx = gibbsWeight fixedEnergy 1 x := by
  simp_rw [gibbsWeight_eq, mul_div_assoc', ← Finset.sum_div, T12_gibbs_sum]

lemma T12_pop0 : (35/100 : ℝ) * T12 0 0 + (25/100 : ℝ) * T12 0 1 + (20/100 : ℝ) * T12 0 2 + (20/100 : ℝ) * T12 0 3 = 1/2 := by
  simp only [T12]
  have hs := s_mul
  have ht := t_mul
  linear_combination 1/10 * hs + 1/20 * ht

lemma T12_pop12 : (35/100 : ℝ) * (T12 1 0 + T12 2 0) + (25/100 : ℝ) * (T12 1 1 + T12 2 1) +
    (20/100 : ℝ) * (T12 1 2 + T12 2 2) + (20/100 : ℝ) * (T12 1 3 + T12 2 3) = 7/20 := by
  simp only [T12]
  have hs := s_mul
  linear_combination -1/10 * hs

lemma T12_pop3 : (35/100 : ℝ) * T12 3 0 + (25/100 : ℝ) * T12 3 1 + (20/100 : ℝ) * T12 3 2 + (20/100 : ℝ) * T12 3 3 = 3/20 := by
  simp only [T12]
  have ht := t_mul
  linear_combination -1/20 * ht

lemma T12_feasible : FixedChoiFeasible (J_of T12) :=
  J_of_feasible T12 T12_nonneg T12_col T12_gibbs T12_pop0 T12_pop12 T12_pop3

lemma cgpOptimum_1_ge : b1 ≤ cgpOptimum 1 := by
  have h_le := channelObjective_le_cgpOptimum 1 (J_of T12) T12_feasible
  rw [J_of_obj1 T12] at h_le
  have h_bound : b1 ≤ (1 / 20 : ℝ) * (Real.sqrt (T12 2 2) * Real.sqrt (T12 3 3)) := by
    have hT22 : (0 : ℝ) ≤ T12 2 2 := T12_nonneg 2 2
    have hT33 : (0 : ℝ) ≤ T12 3 3 := T12_nonneg 3 3
    have hb1_pos : (0 : ℝ) ≤ 20 * b1 := by dsimp [b1]; norm_num
    have h_sq : (20 * b1) ^ 2 ≤ T12 2 2 * T12 3 3 := by
      have hT22_val : T12 2 2 = 1 := rfl
      have hT33_val : T12 3 3 = 1 - t := rfl
      rw [hT22_val, hT33_val, one_mul]
      have h_lin : 1 ≤ (1 - K2) * (4 - 7 * a ^ 3) := by
        have ha3_hi := a3_bounds.2
        dsimp [K2, a3_hi] at *
        linarith
      have h_k2 : K2 ≤ 1 - t := by
        have ht := t_mul
        have hA : 1 * t ≤ (1 - K2) * (4 - 7 * a ^ 3) * t := by
          have ht_pos : 0 < t := by linarith [t_bounds.1]
          nlinarith
        have hB : (1 - K2) * (4 - 7 * a ^ 3) * t = (1 - K2) * (t * (4 - 7 * a ^ 3)) := by ring
        rw [hB, ht, mul_one] at hA
        linarith
      have h_num : (20 * b1) ^ 2 ≤ K2 := by dsimp [b1, K2]; norm_num
      exact le_trans h_num h_k2
    have h_sqrt := le_sqrt_mul_sqrt hb1_pos hT22 hT33 h_sq
    linarith
  linarith

lemma cgpOptimum_2_ge : b2 ≤ cgpOptimum 2 := by
  have h_le := channelObjective_le_cgpOptimum 2 (J_of T12) T12_feasible
  rw [J_of_obj2 T12] at h_le
  have h_bound : b2 ≤ (1 / 25 : ℝ) * (Real.sqrt (T12 0 0) * Real.sqrt (T12 3 3)) := by
    have hT00 : (0 : ℝ) ≤ T12 0 0 := T12_nonneg 0 0
    have hT33 : (0 : ℝ) ≤ T12 3 3 := T12_nonneg 3 3
    have hb2_pos : (0 : ℝ) ≤ 25 * b2 := by dsimp [b2]; norm_num
    have h_sq : (25 * b2) ^ 2 ≤ T12 0 0 * T12 3 3 := by
      have hT00_val : T12 0 0 = 1 - 2 * a * s - a ^ 3 * t := rfl
      have hT33_val : T12 3 3 = 1 - t := rfl
      rw [hT00_val, hT33_val]
      have hs := s_mul
      have ht := t_mul
      have hs_pos : 0 < s := by linarith [s_bounds.1]
      have ht_pos : 0 < t := by linarith [t_bounds.1]
      have ha := a_bounds.2
      have ha3 := a3_bounds.2
      have h_lin1 : 2 * a ≤ M1 * (5 - 7 * a) := by
        dsimp [M1, a_hi] at *
        linarith
      have h_m1 : 2 * a * s ≤ M1 := by
        have hA : 2 * a * s ≤ M1 * (5 - 7 * a) * s := by nlinarith
        have hB : M1 * (5 - 7 * a) * s = M1 * (s * (5 - 7 * a)) := by ring
        rw [hB, hs, mul_one] at hA
        exact hA
      have h_lin2 : a ^ 3 ≤ M2 * (4 - 7 * a ^ 3) := by
        dsimp [M2, a3_hi] at *
        linarith
      have h_m2 : a ^ 3 * t ≤ M2 := by
        have hA : a ^ 3 * t ≤ M2 * (4 - 7 * a ^ 3) * t := by nlinarith
        have hB : M2 * (4 - 7 * a ^ 3) * t = M2 * (t * (4 - 7 * a ^ 3)) := by ring
        rw [hB, ht, mul_one] at hA
        exact hA
      have h_k1 : K1 ≤ 1 - 2 * a * s - a ^ 3 * t := by
        have : K1 = 1 - M1 - M2 := by dsimp [K1, M1, M2]; norm_num
        rw [this]
        linarith
      have h_lin3 : 1 ≤ (1 - K2) * (4 - 7 * a ^ 3) := by
        dsimp [K2, a3_hi] at *
        linarith
      have h_k2 : K2 ≤ 1 - t := by
        have hA : 1 * t ≤ (1 - K2) * (4 - 7 * a ^ 3) * t := by nlinarith
        have hB : (1 - K2) * (4 - 7 * a ^ 3) * t = (1 - K2) * (t * (4 - 7 * a ^ 3)) := by ring
        rw [hB, ht, mul_one] at hA
        linarith
      have hK1_nonneg : (0 : ℝ) ≤ K1 := by dsimp [K1]; norm_num
      have hK2_nonneg : (0 : ℝ) ≤ K2 := by dsimp [K2]; norm_num
      have h_prod : K1 * K2 ≤ (1 - 2 * a * s - a ^ 3 * t) * (1 - t) := by nlinarith
      have h_num : (25 * b2) ^ 2 ≤ K1 * K2 := by dsimp [b2, K1, K2]; norm_num
      exact le_trans h_num h_prod
    have h_sqrt := le_sqrt_mul_sqrt hb2_pos hT00 hT33 h_sq
    linarith
  linarith

def T0 : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 1 - 3 * a * s
  | 0, 1 => 3 * s - 1
  | 0, 2 => 1 - a ^ 2 * u_par
  | 0, 3 => 1 - (3 - 4 * a ^ 2) * u_par
  | 1, 0 => 3 * a * s - a
  | 1, 1 => 2 - 3 * s
  | 1, 2 => 0
  | 1, 3 => 0
  | 2, 0 => a
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => a ^ 2 * u_par
  | 3, 3 => (3 - 4 * a ^ 2) * u_par

lemma T0_nonneg (x u_idx : Fin 4) : 0 ≤ T0 x u_idx := by
  have ha_lo := a_bounds.1
  have ha_hi := a_bounds.2
  have hs_lo := s_bounds.1
  have hs_hi := s_bounds.2
  have hu_lo := u_bounds.1
  have hu_hi := u_bounds.2
  dsimp [a_lo, a_hi] at *
  fin_cases x <;> fin_cases u_idx <;> { simp only [T0]; nlinarith }

lemma T0_col (u_idx : Fin 4) : ∑ x, T0 x u_idx = 1 := by
  fin_cases u_idx <;> { simp only [Fin.sum_univ_four, T0]; ring }

lemma T0_gibbs_sum (x : Fin 4) : ∑ u_idx, T0 x u_idx * G u_idx = G x := by
  fin_cases x
  · simp only [Fin.sum_univ_four, T0, G]
    have hu := u_mul
    linear_combination -a ^ 3 * hu
  · simp only [Fin.sum_univ_four, T0, G]
    ring
  · simp only [Fin.sum_univ_four, T0, G]
    ring
  · simp only [Fin.sum_univ_four, T0, G]
    have hu := u_mul
    linear_combination a ^ 3 * hu

lemma T0_gibbs (x : Fin 4) : ∑ u_idx, T0 x u_idx * gibbsWeight fixedEnergy 1 u_idx = gibbsWeight fixedEnergy 1 x := by
  simp_rw [gibbsWeight_eq, mul_div_assoc', ← Finset.sum_div, T0_gibbs_sum]

lemma T0_pop0 : (35/100 : ℝ) * T0 0 0 + (25/100 : ℝ) * T0 0 1 + (20/100 : ℝ) * T0 0 2 + (20/100 : ℝ) * T0 0 3 = 1/2 := by
  simp only [T0]
  have hs := s_mul
  have hu := u_mul
  linear_combination 3/20 * hs - 3/20 * hu

lemma T0_pop12 : (35/100 : ℝ) * (T0 1 0 + T0 2 0) + (25/100 : ℝ) * (T0 1 1 + T0 2 1) +
    (20/100 : ℝ) * (T0 1 2 + T0 2 2) + (20/100 : ℝ) * (T0 1 3 + T0 2 3) = 7/20 := by
  simp only [T0]
  have hs := s_mul
  linear_combination -3/20 * hs

lemma T0_pop3 : (35/100 : ℝ) * T0 3 0 + (25/100 : ℝ) * T0 3 1 + (20/100 : ℝ) * T0 3 2 + (20/100 : ℝ) * T0 3 3 = 3/20 := by
  simp only [T0]
  have hu := u_mul
  linear_combination 3/20 * hu

lemma T0_feasible : FixedChoiFeasible (J_of T0) :=
  J_of_feasible T0 T0_nonneg T0_col T0_gibbs T0_pop0 T0_pop12 T0_pop3

lemma cgpOptimum_0_ge : b0 ≤ cgpOptimum 0 := by
  have h_le := channelObjective_le_cgpOptimum 0 (J_of T0) T0_feasible
  rw [J_of_obj0 T0] at h_le
  have h_bound : b0 ≤ (1 / 20 : ℝ) * (Real.sqrt (T0 0 0) * Real.sqrt (T0 1 1)) := by
    have hT00 : (0 : ℝ) ≤ T0 0 0 := T0_nonneg 0 0
    have hT11 : (0 : ℝ) ≤ T0 1 1 := T0_nonneg 1 1
    have hb0_pos : (0 : ℝ) ≤ 20 * b0 := by dsimp [b0]; norm_num
    have h_sq : (20 * b0) ^ 2 ≤ T0 0 0 * T0 1 1 := by
      have hT00_val : T0 0 0 = 1 - 3 * a * s := rfl
      have hT11_val : T0 1 1 = 2 - 3 * s := rfl
      rw [hT00_val, hT11_val]
      have hs := s_mul
      have hs_pos : 0 < s := by linarith [s_bounds.1]
      have ha_hi := a_bounds.2
      have h1 : 1 - 3 * a * s = 5 * (1 - 2 * a) * s := by linear_combination -(1 : ℝ) * hs
      have h2 : 2 - 3 * s = 7 * (1 - 2 * a) * s := by linear_combination -(2 : ℝ) * hs
      have h_lin : F * (5 - 7 * a) ≤ 1 - 2 * a := by
        dsimp [F, a_hi] at *
        linarith
      have h_F_le : F ≤ (1 - 2 * a) * s := by
        have hA : F * (5 - 7 * a) * s ≤ (1 - 2 * a) * s := by nlinarith
        have hB : F * (5 - 7 * a) * s = F * (s * (5 - 7 * a)) := by ring
        rw [hB, hs, mul_one] at hA
        exact hA
      have hF_pos : (0 : ℝ) ≤ F := by dsimp [F]; norm_num
      have h_sq_F : F ^ 2 ≤ ((1 - 2 * a) * s) ^ 2 := by nlinarith
      have h_num : (20 * b0) ^ 2 ≤ 35 * F ^ 2 := by dsimp [b0, F]; norm_num
      rw [h1, h2]
      have : 5 * (1 - 2 * a) * s * (7 * (1 - 2 * a) * s) = 35 * ((1 - 2 * a) * s) ^ 2 := by ring
      rw [this]
      nlinarith
    have h_sqrt := le_sqrt_mul_sqrt hb0_pos hT00 hT11 h_sq
    linarith
  linarith

lemma sum_cgpOptimum_ge : (1030097 / 10000000 : ℝ) ≤ ∑ k : Fin 3, cgpOptimum k := by
  simp only [Fin.sum_univ_three]
  have h0 := cgpOptimum_0_ge
  have h1 := cgpOptimum_1_ge
  have h2 := cgpOptimum_2_ge
  have h_sum : b0 + b1 + b2 = (1030097 / 10000000 : ℝ) := by
    dsimp [b0, b1, b2]; norm_num
  linarith

end

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution :
    (1030097/10000000 : ℝ) ≤ (∑ k : Fin 3, cgpOptimum k) ∧
    (1030090/10000000 : ℝ) < 1030097/10000000 ∧
    cgpSumOptimum ≤ (881264/10000000 : ℝ) ∧
    (881264/10000000 : ℝ) < 881270/10000000 := by
  refine ⟨sum_cgpOptimum_ge, by norm_num, cgpSumOptimum_le, by norm_num⟩
