-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.tDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:51:11.563654+00:00
-- url     : https://prove2.me/submissions/0c1afc94-10b5-4b8b-a057-d34caec95bec

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P09
open ErrorMitigation

/-- PDF p.5, §VII: T decomposition; Rz cubed is S up to phase, whereas Rz is S inverse. -/
theorem gk_exp_pi4 : Complex.exp (Complex.I * Real.pi / 4) =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

theorem solution :
    (∀ X : Matrix Bool Bool ℂ,
      conjSuperop gateT X = ∑ i, (tCoefficients i : ℂ) • conjSuperop (tMatrices i) X) ∧
    coefficientMass tCoefficients = Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  refine ⟨fun X => ?_, ?_⟩
  · simp only [conjSuperop, Fin.sum_univ_three, tCoefficients, tMatrices, gateT, tableIMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, gk_exp_pi4]
    have hc : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [← Complex.ofReal_pow, hs]; norm_num
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
      field_simp; rw [hc]
    have hc3 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by rw [pow_succ, hc]
    have hc4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by rw [pow_succ, hc3, mul_assoc, ← pow_two, hc]; norm_num
    have hc5 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 5 = 4 * ((Real.sqrt 2 : ℝ) : ℂ) := by rw [pow_succ, hc4]
    have hc6 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 6 = 8 := by rw [pow_succ, hc5, mul_assoc, ← pow_two, hc]; norm_num
    have hc7 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 7 = 8 * ((Real.sqrt 2 : ℝ) : ℂ) := by rw [pow_succ, hc6]
    have hc8 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 8 = 16 := by rw [pow_succ, hc7, mul_assoc, ← pow_two, hc]; norm_num
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    have hI4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
    have hI5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, hI4, one_mul]
    have hI6 : Complex.I ^ 6 = -1 := by rw [pow_succ, hI5, Complex.I_mul_I]
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.mul_apply, pauliZ, pow_succ, Matrix.diagonal, Fintype.sum_bool, Matrix.smul_apply,
        Complex.conj_ofReal] <;>
      simp only [hinv, map_ofNat] <;> ring_nf <;>
      simp only [hc, hc3, hc4, hc5, hc6, hc7, hc8, Complex.I_sq, hI3, hI4, hI5, hI6] <;> ring_nf
  · simp only [coefficientMass, Fin.sum_univ_three, tCoefficients, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have h1 : 1 ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2), abs_of_nonpos (by linarith),
      abs_of_pos (by positivity)]
    ring

