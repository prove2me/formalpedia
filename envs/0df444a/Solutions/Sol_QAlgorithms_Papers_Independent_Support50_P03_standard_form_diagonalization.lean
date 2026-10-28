-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P03.standard_form_diagonalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:42:41.324705+00:00
-- url     : https://prove2.me/submissions/dbf17bad-6b0e-4f74-abb3-92ed80ba88e3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)
open Matrix
open scoped ComplexOrder

theorem x5ae_cov (a b c : ℝ) :
    standardCovariance a b c = Matrix.fromBlocks !![a, c; c, b] 0 0 !![a, -c; -c, b] := by
  simp only [standardCovariance, standardParity, repeatBlock, standardV0, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- the test-vector inequality extracted from `V + iΩ/2 ⪰ 0`. -/
theorem x5ae_form (a b c : ℝ) (hV : HalfVacuumCovariance (standardCovariance a b c))
    (q1 q2 r1 r2 : ℝ) :
    0 ≤ a * q1 ^ 2 + 2 * c * q1 * q2 + b * q2 ^ 2 + a * r1 ^ 2 - 2 * c * r1 * r2 + b * r2 ^ 2
      - (q1 * r1 + q2 * r2) := by
  obtain ⟨-, -, hpsd⟩ := hV
  set x : Phase 2 → ℂ := fun k => match k with
    | Sum.inl j => (![q1, q2] j : ℂ)
    | Sum.inr j => Complex.I * (![r1, r2] j : ℂ)
  have h := hpsd.dotProduct_mulVec_nonneg x
  rw [x5ae_cov] at h
  have : star x ⬝ᵥ ((complexify (Matrix.fromBlocks !![a, c; c, b] 0 0 !![a, -c; -c, b]) +
      (Complex.I / 2) • complexify (sigma 2)) *ᵥ x) =
      ((a * q1 ^ 2 + 2 * c * q1 * q2 + b * q2 ^ 2 + a * r1 ^ 2 - 2 * c * r1 * r2 + b * r2 ^ 2
      - (q1 * r1 + q2 * r2) : ℝ) : ℂ) := by
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, x, Pi.star_apply,
      Matrix.add_apply, Matrix.smul_apply, complexify, sigma, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
    simp only [Matrix.zero_apply, Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_ne,
      ne_eq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat,
      not_false_eq_true, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    apply Complex.ext <;> simp [pow_two] <;> ring
  rw [this] at h
  exact_mod_cast h

theorem x5ae_scal (a b c : ℝ) (hV : HalfVacuumCovariance (standardCovariance a b c)) :
    1 / 2 ≤ a ∧ 1 / 2 ≤ b ∧ 4 * c ^ 2 ≤ (2 * a - 1) * (2 * b + 1) ∧
      4 * c ^ 2 ≤ (2 * a + 1) * (2 * b - 1) := by
  have h1 := x5ae_form a b c hV 1 0 1 0
  have h2 := x5ae_form a b c hV 0 1 0 1
  have ha : 1 / 2 ≤ a := by nlinarith
  have hb : 1 / 2 ≤ b := by nlinarith
  have h3 := x5ae_form a b c hV (2 * b + 1) (-2 * c) (2 * b + 1) (2 * c)
  have h4 := x5ae_form a b c hV (-2 * c) (2 * a + 1) (2 * c) (2 * a + 1)
  refine ⟨ha, hb, ?_, ?_⟩
  · have e : 0 ≤ (2 * b + 1) * ((2 * a - 1) * (2 * b + 1) - 4 * c ^ 2) := by nlinarith
    have hpos : 0 < 2 * b + 1 := by linarith
    nlinarith [(mul_nonneg_iff_of_pos_left hpos).mp e]
  · have e : 0 ≤ (2 * a + 1) * ((2 * a + 1) * (2 * b - 1) - 4 * c ^ 2) := by nlinarith
    have hpos : 0 < 2 * a + 1 := by linarith
    nlinarith [(mul_nonneg_iff_of_pos_left hpos).mp e]

theorem x5ae_y (a b c : ℝ) (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b)
    (h3 : 4 * c ^ 2 ≤ (2 * a - 1) * (2 * b + 1)) (h4 : 4 * c ^ 2 ≤ (2 * a + 1) * (2 * b - 1)) :
    1 ≤ standardY a b c ∧ (1 + b - a) ^ 2 ≤ standardY a b c ∧ (1 + a - b) ^ 2 ≤ standardY a b c ∧
      standardY a b c ≤ (a + b) ^ 2 := by
  unfold standardY
  refine ⟨by nlinarith [sq_nonneg (a - b)], by nlinarith, by nlinarith, by nlinarith⟩

theorem x5ae_omega (a b c : ℝ) (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b)
    (h3 : 4 * c ^ 2 ≤ (2 * a - 1) * (2 * b + 1)) (h4 : 4 * c ^ 2 ≤ (2 * a + 1) * (2 * b - 1)) :
    let s := Real.sqrt (standardY a b c)
    0 < s ∧ s ^ 2 = standardY a b c ∧ s ≤ a + b ∧
    standardOmegaPlus a b c ^ 2 = (a + b + s) / (2 * s) ∧
    standardOmegaMinus a b c ^ 2 = (a + b - s) / (2 * s) ∧
    standardOmegaPlus a b c * standardOmegaMinus a b c = c / s := by
  intro s
  obtain ⟨hy1, -, -, hy4⟩ := x5ae_y a b c ha hb h3 h4
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = standardY a b c := Real.sq_sqrt (by linarith)
  have hsab : s ≤ a + b := by
    rw [show s = Real.sqrt (standardY a b c) from rfl]
    rw [Real.sqrt_le_left (by linarith)]; exact hy4
  have hP : 0 ≤ (a + b + s) / (2 * s) := by positivity
  have hQ : 0 ≤ (a + b - s) / (2 * s) := div_nonneg (by linarith) (by positivity)
  have hp2 : standardOmegaPlus a b c ^ 2 = (a + b + s) / (2 * s) := Real.sq_sqrt hP
  have hPQ : (a + b + s) / (2 * s) * ((a + b - s) / (2 * s)) = (c / s) ^ 2 := by
    unfold standardY at hs2
    field_simp
    nlinarith [hs2]
  refine ⟨hs0, hs2, hsab, hp2, ?_, ?_⟩
  · unfold standardOmegaMinus
    split_ifs with hc hc'
    · have : s = a + b := by
        rw [show s = Real.sqrt (standardY a b c) from rfl, standardY, hc]
        simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
        exact Real.sqrt_sq (by linarith)
      rw [this]; simp
    · rw [mul_pow, one_pow, one_mul]; exact Real.sq_sqrt hQ
    · rw [mul_pow, neg_one_sq, one_mul]; exact Real.sq_sqrt hQ
  · unfold standardOmegaMinus standardOmegaPlus
    split_ifs with hc hc'
    · rw [hc]; simp
    · rw [one_mul, ← Real.sqrt_mul hP, hPQ, Real.sqrt_sq (div_nonneg hc'.le hs0.le)]
    · rw [neg_one_mul, mul_neg, ← Real.sqrt_mul hP, hPQ, Real.sqrt_sq_eq_abs,
        abs_of_neg (div_neg_of_neg_of_pos (lt_of_le_of_ne (not_lt.mp hc') hc) hs0), neg_neg]

theorem x5ae_S (a b c : ℝ) : standardS a b c =
    Matrix.fromBlocks (standardS0 a b c) 0 0 (pauliZ * standardS0 a b c * pauliZ) := by
  simp only [standardS, standardParity, repeatBlock, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]

theorem x5ae_ZXZ (X : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ) :
    pauliZ * X * pauliZ * Matrix.diagonal d * (pauliZ * X * pauliZ)ᵀ =
      pauliZ * (X * Matrix.diagonal d * Xᵀ) * pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> ring

theorem x5ae_quad (p q u v : ℝ) :
    !![p, q; q, p] * Matrix.diagonal ![u, v] * (!![p, q; q, p])ᵀ =
      !![p ^ 2 * u + q ^ 2 * v, p * q * u + q * p * v; p * q * u + q * p * v,
        q ^ 2 * u + p ^ 2 * v] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal] <;> ring

theorem x5ae_main (a b c : ℝ)
    (hV : HalfVacuumCovariance (standardCovariance a b c)) :
    (1 / 2 : ℝ) ≤ a ∧ (1 / 2 : ℝ) ≤ b ∧
    |c| ≤ min (Real.sqrt ((a - 1 / 2) * (b + 1 / 2)))
      (Real.sqrt ((a + 1 / 2) * (b - 1 / 2))) ∧
    0 < standardY a b c ∧
    (∀ j, (1 / 2 : ℝ) ≤ standardSpectrum a b c j) ∧
    standardV0 a b c = standardS0 a b c * Matrix.diagonal (standardSpectrum a b c) *
      (standardS0 a b c).transpose ∧
    standardS a b c ∈ Matrix.symplecticGroup (Fin 2) ℝ ∧
    standardCovariance a b c = standardS a b c *
      thermalCovariance (standardSpectrum a b c) * (standardS a b c).transpose ∧
    (FaithfulSpectrum (standardSpectrum a b c) →
      gibbsMatrix (standardS a b c) (standardSpectrum a b c) =
        (-2 : ℝ) • (sigma 2 * standardParity * repeatBlock (standardReducedGibbs a b c) *
          standardParity * sigma 2)) := by
  obtain ⟨ha, hb, h3, h4⟩ := x5ae_scal a b c hV
  obtain ⟨hy1, hy2, hy3, hy4⟩ := x5ae_y a b c ha hb h3 h4
  obtain ⟨hs0, hs2, hsab, hp2, hm2, hpm⟩ := x5ae_omega a b c ha hb h3 h4
  set s := Real.sqrt (standardY a b c) with hsdef
  set wp := standardOmegaPlus a b c
  set wm := standardOmegaMinus a b c
  have hsne : s ≠ 0 := hs0.ne'
  have hpm' : wp ^ 2 - wm ^ 2 = 1 := by
    rw [hp2, hm2]; field_simp; ring
  have hV0 : standardV0 a b c = standardS0 a b c * Matrix.diagonal (standardSpectrum a b c) *
      (standardS0 a b c).transpose := by
    have hS0 : standardS0 a b c = !![wp, wm; wm, wp] := rfl
    have hD : standardSpectrum a b c = ![(s - (b - a)) / 2, (s + (b - a)) / 2] := rfl
    rw [hS0, hD, x5ae_quad]
    have e00 : wp ^ 2 * ((s - (b - a)) / 2) + wm ^ 2 * ((s + (b - a)) / 2) = a := by
      rw [hp2, hm2]; field_simp; ring
    have e11 : wm ^ 2 * ((s - (b - a)) / 2) + wp ^ 2 * ((s + (b - a)) / 2) = b := by
      rw [hp2, hm2]; field_simp; ring
    have e01 : wp * wm * ((s - (b - a)) / 2) + wm * wp * ((s + (b - a)) / 2) = c := by
      have : wp * wm * ((s - (b - a)) / 2) + wm * wp * ((s + (b - a)) / 2) = (wp * wm) * s := by
        ring
      rw [this, hpm]; field_simp
    ext i j; fin_cases i <;> fin_cases j <;> simp [standardV0, e00, e11, e01]
  refine ⟨ha, hb, ?_, by linarith, ?_, hV0, ?_, ?_, ?_⟩
  · refine le_min (Real.abs_le_sqrt (by nlinarith)) (Real.abs_le_sqrt (by nlinarith))
  · intro j
    have hsq : ∀ t : ℝ, t ^ 2 ≤ standardY a b c → t ≤ s := fun t ht => by
      have := Real.sqrt_le_sqrt ht
      rw [Real.sqrt_sq_eq_abs] at this
      exact (le_abs_self t).trans this
    fin_cases j
    · have := hsq _ hy2; simp [standardSpectrum, ← hsdef]; linarith
    · have := hsq _ hy3; simp [standardSpectrum, ← hsdef]; linarith
  · rw [SymplecticGroup.mem_iff, x5ae_S, Matrix.J, fromBlocks_transpose,
      fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.transpose_zero]
    have hS0 : standardS0 a b c = !![wp, wm; wm, wp] := rfl
    rw [hS0]
    congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first | ring1 | linear_combination hpm' | linear_combination -hpm'
  · rw [x5ae_cov, x5ae_S, thermalCovariance, fromBlocks_transpose, fromBlocks_multiply,
      fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.transpose_zero]
    rw [x5ae_ZXZ, ← hV0]
    congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [standardV0, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · intro _
    rw [gibbsMatrix]
    congr 1
    have hL : standardS a b c * thermalCovariance (fun j => realArcoth (2 * standardSpectrum a b c j)) *
        (standardS a b c).transpose =
        standardParity * repeatBlock (standardReducedGibbs a b c) * standardParity := by
      rw [x5ae_S, thermalCovariance, fromBlocks_transpose, fromBlocks_multiply,
        fromBlocks_multiply, standardParity, repeatBlock, fromBlocks_multiply, fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.transpose_zero,
        Matrix.one_mul, Matrix.mul_one]
      rw [x5ae_ZXZ]
      have hsym : (standardS0 a b c).transpose = standardS0 a b c := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [standardS0]
      rw [hsym, standardReducedGibbs]
    rw [show sigma 2 * standardS a b c *
        thermalCovariance (fun j => realArcoth (2 * standardSpectrum a b c j)) *
        (standardS a b c).transpose * sigma 2 = sigma 2 * (standardS a b c *
        thermalCovariance (fun j => realArcoth (2 * standardSpectrum a b c j)) *
        (standardS a b c).transpose) * sigma 2 by simp only [Matrix.mul_assoc], hL]
    simp only [Matrix.mul_assoc]

end QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Support50.P03
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

theorem solution (a b c : ℝ)
    (hV : HalfVacuumCovariance (standardCovariance a b c)) :
    (1 / 2 : ℝ) ≤ a ∧ (1 / 2 : ℝ) ≤ b ∧
    |c| ≤ min (Real.sqrt ((a - 1 / 2) * (b + 1 / 2)))
      (Real.sqrt ((a + 1 / 2) * (b - 1 / 2))) ∧
    0 < standardY a b c ∧
    (∀ j, (1 / 2 : ℝ) ≤ standardSpectrum a b c j) ∧
    standardV0 a b c = standardS0 a b c * Matrix.diagonal (standardSpectrum a b c) *
      (standardS0 a b c).transpose ∧
    standardS a b c ∈ Matrix.symplecticGroup (Fin 2) ℝ ∧
    standardCovariance a b c = standardS a b c *
      thermalCovariance (standardSpectrum a b c) * (standardS a b c).transpose ∧
    (FaithfulSpectrum (standardSpectrum a b c) →
      gibbsMatrix (standardS a b c) (standardSpectrum a b c) =
        (-2 : ℝ) • (sigma 2 * standardParity * repeatBlock (standardReducedGibbs a b c) *
          standardParity * sigma 2)) :=
  x5ae_main a b c hV
