-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.thermalFullRank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:56:35.690467+00:00
-- url     : https://prove2.me/submissions/2f305c8b-e2d4-4c7a-b3a3-4ce62c9c07ab

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

open QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

namespace G56DM

open QAlgorithms.Papers.Independent.Independent2.P01 (damping dampingKraus) in
lemma fd (g : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    finDamping g ρ i j = QAlgorithms.krausApply (dampingKraus g)
      (Matrix.of fun b c => ρ (cond b 1 0) (cond c 1 0)) (i.val == 1) (j.val == 1) := rfl

lemma fd00 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 0 0 = ρ 0 0 + (g : ℂ) * ρ 1 1 := by
  have h2 : (Real.sqrt g : ℂ) * (Real.sqrt g : ℂ) = (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]
  linear_combination (ρ 1 1) * h2

lemma fd11 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 1 1 = (1 - (g : ℂ)) * ρ 1 1 := by
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]
  linear_combination (ρ 1 1) * h1

lemma fd01 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 0 1 = (Real.sqrt (1 - g) : ℂ) * ρ 0 1 := by
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]
  ring

lemma fd10 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g ρ 1 0 = (Real.sqrt (1 - g) : ℂ) * ρ 1 0 := by
  rw [fd]
  simp only [QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, QAlgorithms.krausApply, Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [
    Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Complex.conj_ofReal]

end G56DM

namespace G56TF

open G56DM

lemma th (g n : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalChannel g n X 0 0 = (1 - n) * (X 0 0 + g * X 1 1) + n * (1 - g) * X 0 0 ∧
    thermalChannel g n X 1 1 = (1 - n) * (1 - g) * X 1 1 + n * (X 1 1 + g * X 0 0) ∧
    thermalChannel g n X 0 1 = (Real.sqrt (1 - g) : ℂ) * X 0 1 ∧
    thermalChannel g n X 1 0 = (Real.sqrt (1 - g) : ℂ) * X 1 0 := by
  have hF : ∀ Y : Matrix (Fin 2) (Fin 2) ℂ, ∀ i j, ((!![0, 1; 1, 0] * Y * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) i j =
      Y (1 - i) (1 - j) := by
    intro Y i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have e0 : (1 : Fin 2) - 0 = 1 := rfl
  have e1 : (1 : Fin 2) - 1 = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [thermalChannel, Matrix.add_apply, Matrix.smul_apply, hF, e0, e1, fd00 g hg0 hg1, fd11 g hg0 hg1,
    fd01 g hg0 hg1, fd10 g hg0 hg1, Complex.real_smul] <;> push_cast <;> ring

end G56TF

namespace G56TF

open G56DM QAlgorithms

lemma t00 (X : Matrix (Fin 2) (Fin 2) ℂ) : thermalChannel (1/2) (1/10) X 0 0 = (1 - (1/10 : ℝ)) * (X 0 0 + (1/2 : ℝ) * X 1 1) + (1/10 : ℝ) * (1 - (1/2 : ℝ)) * X 0 0 :=
  (th (1/2) (1/10) (by norm_num) (by norm_num) X).1
lemma t11 (X : Matrix (Fin 2) (Fin 2) ℂ) : thermalChannel (1/2) (1/10) X 1 1 = (1 - (1/10 : ℝ)) * (1 - (1/2 : ℝ)) * X 1 1 + (1/10 : ℝ) * (X 1 1 + (1/2 : ℝ) * X 0 0) :=
  (th (1/2) (1/10) (by norm_num) (by norm_num) X).2.1
lemma t01 (X : Matrix (Fin 2) (Fin 2) ℂ) : thermalChannel (1/2) (1/10) X 0 1 = (Real.sqrt (1 - 1/2) : ℂ) * X 0 1 :=
  (th (1/2) (1/10) (by norm_num) (by norm_num) X).2.2.1
lemma t10 (X : Matrix (Fin 2) (Fin 2) ℂ) : thermalChannel (1/2) (1/10) X 1 0 = (Real.sqrt (1 - 1/2) : ℂ) * X 1 0 :=
  (th (1/2) (1/10) (by norm_num) (by norm_num) X).2.2.2

def c : ℂ := (Real.sqrt (1 - 1/2) : ℂ)

def TSm : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.of fun p q =>
  if p = q then (if p = (0,0) then 19/40 else if p = (0,1) then 1/40 else if p = (1,0) then 9/40 else 11/40)
  else if (p = (0,0) ∧ q = (1,1)) ∨ (p = (1,1) ∧ q = (0,0)) then c / 2 else 0

lemma bell_sq : ((Real.sqrt ((2 : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((2 : ℕ) : ℝ) : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma ts_eq : thermalState = TSm := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, thermalState, choi, QAlgorithms.idTensorSuperop, Matrix.of_apply, t00, t11, t01, t10] <;>
    simp [pureDensity, bellVector, TSm, c, Complex.conj_ofReal] <;>
    ring_nf <;> simp only [inv_pow, hs2] <;> norm_num
end G56TF

namespace G56TF

open G56DM QAlgorithms

lemma c_sq : c * c = 1 / 2 := by
  unfold c; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma c_real : starRingEnd ℂ c = c := by unfold c; exact Complex.conj_ofReal _

lemma TS_herm : TSm.IsHermitian := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [TSm, Matrix.conjTranspose_apply, c_real]

lemma TS_quad (x : Fin 2 × Fin 2 → ℂ) :
    star x ⬝ᵥ (TSm *ᵥ x) = (((19/40 : ℝ) * Complex.normSq (x (0,0)) + (1/40 : ℝ) * Complex.normSq (x (0,1)) +
      (9/40 : ℝ) * Complex.normSq (x (1,0)) + (11/40 : ℝ) * Complex.normSq (x (1,1)) +
      (Real.sqrt (1 - 1/2)) * ((x (0,0)).re * (x (1,1)).re + (x (0,0)).im * (x (1,1)).im) : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, TSm, Matrix.of_apply,
    Pi.star_apply]
  apply Complex.ext <;>
    simp [c, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.div_re, Complex.div_im] <;> ring

lemma TS_posdef : TSm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos TS_herm fun x hx => ?_
  rw [TS_quad]
  have hs : Real.sqrt (1 - 1/2) * Real.sqrt (1 - 1/2) = 1/2 := by rw [Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt (1 - 1/2) := Real.sqrt_nonneg _
  have hpos : 0 < Complex.normSq (x (0,0)) + Complex.normSq (x (0,1)) + Complex.normSq (x (1,0)) +
      Complex.normSq (x (1,1)) := by
    by_contra h
    push Not at h
    apply hx
    have h0 := Complex.normSq_nonneg (x (0,0)); have h1 := Complex.normSq_nonneg (x (0,1))
    have h2 := Complex.normSq_nonneg (x (1,0)); have h3 := Complex.normSq_nonneg (x (1,1))
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp <;> apply Complex.normSq_eq_zero.mp <;> linarith
  have key : (1/400 : ℝ) * (Complex.normSq (x (0,0)) + Complex.normSq (x (0,1)) + Complex.normSq (x (1,0)) +
      Complex.normSq (x (1,1))) ≤ (19/40 : ℝ) * Complex.normSq (x (0,0)) + (1/40 : ℝ) * Complex.normSq (x (0,1)) +
      (9/40 : ℝ) * Complex.normSq (x (1,0)) + (11/40 : ℝ) * Complex.normSq (x (1,1)) +
      (Real.sqrt (1 - 1/2)) * ((x (0,0)).re * (x (1,1)).re + (x (0,0)).im * (x (1,1)).im) := by
    simp only [Complex.normSq_apply]
    set s := Real.sqrt (1 - 1/2)
    nlinarith [sq_nonneg (2 * (189/400) * (x (0,0)).re + s * (x (1,1)).re),
      sq_nonneg (2 * (189/400) * (x (0,0)).im + s * (x (1,1)).im),
      mul_self_nonneg (x (0,1)).re, mul_self_nonneg (x (0,1)).im, mul_self_nonneg (x (1,0)).re,
      mul_self_nonneg (x (1,0)).im, mul_self_nonneg (x (1,1)).re, mul_self_nonneg (x (1,1)).im]
  exact_mod_cast (show (0:ℝ) < _ from lt_of_lt_of_le (by positivity) key)

end G56TF

namespace G56TF

open G56DM QAlgorithms

lemma det_shift (r : ℂ) : (Matrix.scalar (Fin 2 × Fin 2) r - TSm).det =
    (r - 19/40) * (r - 11/40) * (r - 1/40) * (r - 9/40) - (r - 1/40) * (r - 9/40) * (c / 2) * (c / 2) := by
  rw [← Matrix.det_reindex_self finProdFinEquiv]
  have hN : Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.scalar (Fin 2 × Fin 2) r - TSm) =
      !![r - 19/40, 0, 0, -(c/2); 0, r - 1/40, 0, 0; 0, 0, r - 9/40, 0; -(c/2), 0, 0, r - 11/40] := by
    have e0 : finProdFinEquiv.symm (0 : Fin 4) = ((0 : Fin 2), (0 : Fin 2)) := by decide
    have e1 : finProdFinEquiv.symm (1 : Fin 4) = ((0 : Fin 2), (1 : Fin 2)) := by decide
    have e2 : finProdFinEquiv.symm (2 : Fin 4) = ((1 : Fin 2), (0 : Fin 2)) := by decide
    have e3 : finProdFinEquiv.symm (3 : Fin 4) = ((1 : Fin 2), (1 : Fin 2)) := by decide
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, e0, e1, e2, e3, TSm, Matrix.scalar_apply,
        Matrix.diagonal_apply, Prod.ext_iff]
  rw [hN, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

end G56TF

open QAlgorithms G56DM G56TF in
theorem solution :
    let eig : Fin 4 → ℝ := ![(15 + 6 * Real.sqrt 6) / 40,
      (15 - 6 * Real.sqrt 6) / 40, 1 / 40, 9 / 40]
    IsDensityMatrix thermalState ∧ thermalState.PosDef ∧
    traceRight thermalState = maximallyMixed 2 ∧
    traceLeft thermalState = (!![(7 / 10 : ℂ), 0; 0, 3 / 10]) ∧
    thermalState.charpoly = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (eig i : ℂ)) ∧
    (∀ i, 0 < eig i) ∧
    thermalChannel (1 / 2) (1 / 10) 1 ≠ 1 ∧
    (∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsPure rho →
      ¬ IsPure (thermalChannel (1 / 2) (1 / 10) rho)) := by
  intro eig
  have h6 : ((Real.sqrt 6 : ℝ) : ℂ) * ((Real.sqrt 6 : ℝ) : ℂ) = 6 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [ts_eq]
  refine ⟨⟨TS_posdef.posSemidef, ?_⟩, TS_posdef, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.trace, Fintype.sum_prod_type, TSm]; norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [traceRight, TSm, maximallyMixed, Fin.sum_univ_two] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [traceLeft, TSm, Fin.sum_univ_two] <;> norm_num
  · apply Polynomial.funext
    intro r
    rw [Matrix.eval_charpoly, det_shift]
    rw [Fin.prod_univ_four]
    simp [eig]
    linear_combination (-(r - 1/40) * (r - 9/40) / 4) * c_sq + ((r - 1/40) * (r - 9/40) * (36/1600)) * h6
  · have hs := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
    have hs0 := Real.sqrt_nonneg 6
    intro i
    fin_cases i <;> simp [eig] <;> nlinarith
  · intro h
    have := congrFun (congrFun h 0) 0
    rw [t00] at this
    simp at this
    norm_num at this
  · rintro ρ ⟨v, hv, rfl⟩ ⟨w, -, hw⟩
    set σ := thermalChannel (1 / 2) (1 / 10) (pureDensity v)
    have hdw : σ.det = 0 := by
      rw [hw, Matrix.det_fin_two]; simp [pureDensity]; ring
    have hn : Complex.normSq (v 0) + Complex.normSq (v 1) = 1 := by
      have := EuclideanSpace.norm_sq_eq v
      rw [hv, Fin.sum_univ_two] at this
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; linarith
    have hv0 : v 0 * starRingEnd ℂ (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj _
    have hv1 : v 1 * starRingEnd ℂ (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj _
    set a := Complex.normSq (v 0)
    set b := Complex.normSq (v 1)
    have hdet : σ.det = ((((9/10) * (a + b/2) + a/20) * ((9/20) * b + (b + a/2)/10) - a * b / 2 : ℝ) : ℂ) := by
      simp only [σ]
      rw [Matrix.det_fin_two, t00, t11, t01, t10]
      simp only [pureDensity, Matrix.of_apply]
      have hc : (Real.sqrt (1 - 1/2) : ℂ) * (Real.sqrt (1 - 1/2) : ℂ) = 1/2 := c_sq
      rw [hv0, hv1]
      push_cast
      linear_combination (-(v 0 * starRingEnd ℂ (v 1) * (v 1 * starRingEnd ℂ (v 0)))) * hc +
        (-(1/2) * (v 1 * starRingEnd ℂ (v 1))) * hv0 + (-(1/2) * (a : ℂ)) * hv1
    rw [hdet] at hdw
    have hD := Complex.ofReal_eq_zero.mp hdw
    have ha := Complex.normSq_nonneg (v 0)
    have hb := Complex.normSq_nonneg (v 1)
    nlinarith [sq_nonneg (a - 9/10)]
