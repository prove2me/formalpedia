-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P01.werner_partialTranspose_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:31:56.093476+00:00
-- url     : https://prove2.me/submissions/ae04cac4-7f8a-42dd-b732-1db5941733ba

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

/-- Peres PDF p.3, Eqs. (7)–(8): the impure singlet has partial-transpose
eigenvalues `(1+x)/4` three times and `(1-3x)/4` once. For `x < 1/3`
the matrix is positive definite (hence satisfies the necessary criterion). -/
def gp_werner_e : Fin 4 ≃ Bool × Bool where
  toFun := ![(false, false), (false, true), (true, false), (true, true)]
  invFun := fun p => match p with
    | (false, false) => 0 | (false, true) => 1 | (true, false) => 2 | (true, true) => 3
  left_inv := by decide
  right_inv := by decide

theorem solution (x : ℝ) (nonnegative : 0 ≤ x) (fraction : x ≤ 1) :
    (partialTransposeFirst (wernerDensity x)).charpoly =
      (Polynomial.X - Polynomial.C (((1 - 3 * x) / 4 : ℝ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((1 + x) / 4 : ℝ) : ℂ)) ^ 3 ∧
    (x < 1 / 3 → (partialTransposeFirst (wernerDensity x)).PosDef) := by
  set M := partialTransposeFirst (wernerDensity x) with hM
  have hS : M.submatrix gp_werner_e gp_werner_e =
      !![(1 - (x : ℂ)) / 4, 0, 0, -((x : ℂ) / 2);
         0, (1 + (x : ℂ)) / 4, 0, 0;
         0, 0, (1 + (x : ℂ)) / 4, 0;
         -((x : ℂ) / 2), 0, 0, (1 - (x : ℂ)) / 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gp_werner_e, hM, partialTransposeFirst, wernerDensity, singletDensity, pureDensity, ket,
        PiLp.single_apply, Matrix.one_apply] <;> (try ring_nf)
  have hcp : M.charpoly = (M.submatrix gp_werner_e gp_werner_e).charpoly := by
    exact (Matrix.charpoly_reindex gp_werner_e.symm M).symm
  refine ⟨?_, fun hx => ?_⟩
  · rw [hcp, hS]
    apply Polynomial.funext
    intro z
    rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.submatrix_apply,
      show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
    ring
  · let u1 : Bool × Bool → ℂ := fun p => if p = (false, true) then 1 else 0
    let u2 : Bool × Bool → ℂ := fun p => if p = (true, false) then 1 else 0
    let u3 : Bool × Bool → ℂ := fun p =>
      if p = (false, false) then 1 else if p = (true, true) then -1 else 0
    have hdec : M = ((((1 - 3 * x) / 4 : ℝ) : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) +
        (x : ℂ) • (Matrix.vecMulVec u1 (star u1) + Matrix.vecMulVec u2 (star u2) +
          (2⁻¹ : ℂ) • Matrix.vecMulVec u3 (star u3)) := by
      ext p q
      rcases p with ⟨_ | _, _ | _⟩ <;> rcases q with ⟨_ | _, _ | _⟩ <;>
        simp [hM, u1, u2, u3, partialTransposeFirst, wernerDensity, singletDensity, pureDensity, ket,
          PiLp.single_apply, Matrix.one_apply, Matrix.vecMulVec_apply] <;> ring
    have hc : (0 : ℂ) < (((1 - 3 * x) / 4 : ℝ) : ℂ) := Complex.zero_lt_real.mpr (by linarith)
    have hx0 : (0 : ℂ) ≤ (x : ℂ) := Complex.zero_le_real.mpr nonnegative
    have h2 : (0 : ℂ) ≤ (2⁻¹ : ℂ) := by
      rw [Complex.le_def]; norm_num
    rw [hdec]
    exact (Matrix.PosDef.one.smul hc).add_posSemidef
      ((((Matrix.posSemidef_vecMulVec_self_star u1).add
        (Matrix.posSemidef_vecMulVec_self_star u2)).add
        ((Matrix.posSemidef_vecMulVec_self_star u3).smul h2)).smul hx0)

