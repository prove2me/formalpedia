-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P05.permutation_pair_spectra
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:03:14.599866+00:00
-- url     : https://prove2.me/submissions/7bc5c4fc-dcaa-43c3-b9f9-d92cbc2edcfc

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace S110P05B
open QAlgorithms.Papers.Independent.Extend50.P05

open Polynomial

lemma charpoly_blockDiag {o : Type*} [Fintype o] [DecidableEq o] (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.blockDiagonal (fun _ : o => B)).charpoly = B.charpoly ^ Fintype.card o := by
  unfold Matrix.charpoly
  have : Matrix.charmatrix (Matrix.blockDiagonal (fun _ : o => B)) =
      Matrix.blockDiagonal (fun _ : o => Matrix.charmatrix B) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst hkl
      by_cases hij : i = j
      · subst hij; simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply]
      · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, hij]
    · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, hkl]
  rw [this, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]

lemma charpoly_two (a b : ℂ) :
    (!![a, b; b, a] : Matrix (Fin 2) (Fin 2) ℂ).charpoly = (X - C (a + b)) * (X - C (a - b)) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  simp only [C_add, C_sub, C_mul]
  ring


def Wm (d : ℕ) : Matrix (CloningChoiBasis d 2) (Fin 2 × Fin d) ℂ :=
  fun X p => if p.1 = 0 then cupOne d p.2 X else cupTwo d p.2 X

lemma W_mul (d : ℕ) : Wm d * (Wm d)ᴴ = cupOperatorOne d + cupOperatorTwo d := by
  ext X Y
  simp [Wm, Matrix.mul_apply, Matrix.conjTranspose_apply, cupOperatorOne, cupOperatorTwo,
    Fintype.sum_prod_type, Fin.sum_univ_two]

lemma W_gram (d : ℕ) : (Wm d)ᴴ * Wm d = Matrix.blockDiagonal (fun _ : Fin d => !![(d : ℂ), 1; 1, (d : ℂ)]) := by
  ext ⟨k, i⟩ ⟨l, j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  simp_rw [← (finTwoArrowEquiv (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  fin_cases k <;> fin_cases l <;>
  simp [Wm, Matrix.conjTranspose_apply, cupOne, cupTwo, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] <;>
  (try simp only [apply_ite (starRingEnd ℂ), map_one, map_zero]) <;>
  simp [Finset.sum_ite_eq', ite_and, eq_comm]


def Jm (d : ℕ) : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  Matrix.blockDiagonal (fun _ : Fin d => !![(0 : ℂ), 1; 1, 0])

lemma W_cycle (d : ℕ) : Wm d * (Jm d * (Wm d)ᴴ) = cycleOperator d + (cycleOperator d)ᴴ := by
  ext X Y
  simp [Wm, Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, cycleOperator, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma J_gram (d : ℕ) : Jm d * ((Wm d)ᴴ * Wm d) =
    Matrix.blockDiagonal (fun _ : Fin d => !![(1 : ℂ), d; d, 1]) := by
  rw [W_gram, Jm, ← Matrix.blockDiagonal_mul]
  congr 1
  funext k
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end S110P05B
end QAlgorithms.Papers.Independent.Extend50.P05
open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P05
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open Polynomial in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (cupOperatorOne d + cupOperatorTwo d).charpoly =
      (Polynomial.X - Polynomial.C ((d : ℂ) + 1)) ^ d *
      (Polynomial.X - Polynomial.C ((d : ℂ) - 1)) ^ d *
      Polynomial.X ^ (d ^ 3 - 2 * d) ∧
    (cycleOperator d + (cycleOperator d)ᴴ).charpoly =
      (Polynomial.X - Polynomial.C ((d : ℂ) + 1)) ^ d *
      (Polynomial.X + Polynomial.C ((d : ℂ) - 1)) ^ d *
      Polynomial.X ^ (d ^ 3 - 2 * d) := by
  have hle : 2 * d ≤ d ^ 3 := by nlinarith [Nat.mul_le_mul hd hd]
  have e1 : Fintype.card (CloningChoiBasis d 2) = 2 * d + (d ^ 3 - 2 * d) := by
    rw [Nat.add_sub_cancel' hle]; simp; ring
  have e2 : Fintype.card (Fin 2 × Fin d) = 2 * d := by simp
  have hX : (X : ℂ[X]) ^ (2 * d) ≠ 0 := pow_ne_zero _ X_ne_zero
  constructor
  · have h := Matrix.charpoly_mul_comm' (QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.Wm d) (QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.Wm d)ᴴ
    rw [QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.W_mul, QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.W_gram, QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.charpoly_blockDiag, QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.charpoly_two, e1, e2,
      Fintype.card_fin] at h
    apply mul_left_cancel₀ hX
    rw [h, pow_add, mul_pow]
    simp only [C_add, C_sub, map_one]
    ring
  · have h := Matrix.charpoly_mul_comm' (QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.Wm d) (QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.Jm d * (QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.Wm d)ᴴ)
    rw [QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.W_cycle, Matrix.mul_assoc, QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.J_gram, QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.charpoly_blockDiag,
      QAlgorithms.Papers.Independent.Extend50.P05.S110P05B.charpoly_two, e1, e2, Fintype.card_fin] at h
    apply mul_left_cancel₀ hX
    rw [h, pow_add, mul_pow]
    simp only [C_add, C_sub, map_one]
    ring

end
