-- Prove2me | solution 1 for complex_posSemidef_det_le_prod_diag_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:51:47.88967+00:00
-- url     : https://prove2.me/submissions/294562aa-895b-4fa6-801b-427fd71033cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_complex_posSemidef_eq_gram
import Theorems.Thm_complex_gram_det_le_prod_col_sq
import Mathlib.Analysis.Matrix.PosDef
open scoped ComplexOrder

theorem solution {idx : Type*} [Fintype idx] [DecidableEq idx]
    (M : Matrix idx idx Complex) (hM : M.PosSemidef) :
    (M.det.re : Real) ≤ Finset.prod Finset.univ (fun i : idx => ((M i i).re : Real)) := by
  classical
  obtain ⟨A, rfl⟩ := complex_posSemidef_eq_gram M hM
  have hdet := complex_gram_det_le_prod_col_sq A
  have hdiag (i : idx) :
      ((Matrix.conjTranspose A * A) i i).re =
        Finset.sum Finset.univ (fun j : idx => norm (A j i) ^ 2) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
    rw [Complex.re_sum (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [RCLike.mul_self_norm, pow_two]
  calc
    (Matrix.conjTranspose A * A).det.re ≤
        Finset.prod Finset.univ (fun i : idx =>
          Finset.sum Finset.univ (fun j : idx => norm (A j i) ^ 2)) := hdet
    _ = Finset.prod Finset.univ (fun i : idx =>
        ((Matrix.conjTranspose A * A) i i).re) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hdiag i).symm
