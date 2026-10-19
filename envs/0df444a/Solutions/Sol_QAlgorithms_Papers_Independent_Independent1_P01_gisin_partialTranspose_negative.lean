-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P01.gisin_partialTranspose_negative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:15:33.582619+00:00
-- url     : https://prove2.me/submissions/91336151-b04a-4156-ac82-b36e0cd5c037

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P01
open QAlgorithms.Entanglement

/-- Peres PDF p.4, Eqs. (9)–(13): above the strict threshold, the partial
transpose has both negative determinant and a negative eigenvalue. -/
def gp_gisin_e : Fin 4 ≃ Bool × Bool where
  toFun := ![(false, false), (false, true), (true, false), (true, true)]
  invFun := fun p => match p with
    | (false, false) => 0 | (false, true) => 1 | (true, false) => 2 | (true, true) => 3
  left_inv := by decide
  right_inv := by decide

theorem gp_gisin_psd_of_asc {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : M.IsHermitian) (hk : ∀ k, 0 ≤ ascEigenvalues M k) : M.PosSemidef := by
  rw [h.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have := hk (Fin.rev ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))
  simp only [ascEigenvalues, h, dif_pos, Fin.rev_rev] at this
  exact this

theorem solution (x : ℝ) (a b : ℂ)
    (normalized : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (nonnegative : 0 ≤ x) (fraction : x ≤ 1)
    (threshold : (1 + 2 * ‖a * b‖)⁻¹ < x) :
    (partialTransposeFirst (gisinDensity x a b)).det.re < 0 ∧
      ∃ k, ascEigenvalues (partialTransposeFirst (gisinDensity x a b)) k < 0 := by
  set M := partialTransposeFirst (gisinDensity x a b) with hM
  have hS : M.submatrix gp_gisin_e gp_gisin_e =
      !![((1 - x) / 2 : ℂ), 0, 0, x * b * (starRingEnd ℂ) a;
         0, x * a * (starRingEnd ℂ) a, 0, 0;
         0, 0, x * b * (starRingEnd ℂ) b, 0;
         x * a * (starRingEnd ℂ) b, 0, 0, ((1 - x) / 2 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gp_gisin_e, hM, partialTransposeFirst, gisinDensity, pureDensity, ket,
        PiLp.single_apply] <;> ring
  have ha : ((‖a‖ : ℝ) : ℂ) ^ 2 = a * (starRingEnd ℂ) a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hb : ((‖b‖ : ℝ) : ℂ) ^ 2 = b * (starRingEnd ℂ) b := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hdet : M.det =
      ((x ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2 * ((1 - x) ^ 2 / 4 - x ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2) : ℝ) : ℂ) := by
    rw [← Matrix.det_submatrix_equiv_self gp_gisin_e, hS]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
    rw [ha, hb]
    ring
  have hab : ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul a b
  have hpos' : 0 < 1 + 2 * ‖a * b‖ := by positivity
  have h1' : 1 < x * (1 + 2 * ‖a * b‖) := by
    have := mul_lt_mul_of_pos_right threshold hpos'
    rwa [inv_mul_cancel₀ hpos'.ne'] at this
  rw [hab] at h1'
  set t := ‖a‖ * ‖b‖ with ht
  have t0 : 0 ≤ t := by positivity
  have h1 : 1 < x * (1 + 2 * t) := h1'
  have hx0 : 0 < x := by nlinarith
  have hxt : (1 - x) / 2 < x * t := by linarith
  have hsq : (1 - x) ^ 2 / 4 < (x * t) ^ 2 := by nlinarith
  have hxt0 : 0 < x * t := by nlinarith
  have hre : M.det.re < 0 := by
    rw [hdet, Complex.ofReal_re]
    have : x ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2 * ((1 - x) ^ 2 / 4 - x ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2) =
        (x * t) ^ 2 * ((1 - x) ^ 2 / 4 - (x * t) ^ 2) := by rw [ht]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  refine ⟨hre, ?_⟩
  have hHerm : M.IsHermitian := by
    ext p q
    rcases p with ⟨_ | _, _ | _⟩ <;> rcases q with ⟨_ | _, _ | _⟩ <;>
      simp [hM, partialTransposeFirst, gisinDensity, pureDensity, ket, PiLp.single_apply] <;> (try ring_nf) <;> (try simp)
  by_contra hc
  push Not at hc
  have hpsd := gp_gisin_psd_of_asc M hHerm hc
  have := (Complex.le_def.mp hpsd.det_nonneg).1
  simp only [Complex.zero_re] at this
  linarith

