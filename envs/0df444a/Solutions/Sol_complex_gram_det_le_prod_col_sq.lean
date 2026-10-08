-- Prove2me | solution 1 for complex_gram_det_le_prod_col_sq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T21:41:34.766957+00:00
-- url     : https://prove2.me/submissions/2d87049a-ed88-431b-b2c3-6eb8072be180
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Matrix.PosDef
import Theorems.Thm_complex_psd_det_le_prod_diag
open scoped ComplexOrder

theorem solution {idx : Type*} [Fintype idx] [DecidableEq idx]
    (A : Matrix idx idx Complex) :
    (Matrix.conjTranspose A * A).det.re <=
      Finset.prod Finset.univ (fun i : idx =>
        Finset.sum Finset.univ (fun j : idx => norm (A j i) ^ 2)) := by
  let G := Matrix.conjTranspose A * A
  have h := complex_psd_det_le_prod_diag G
    (Matrix.posSemidef_conjTranspose_mul_self A)
  have hd : Finset.prod Finset.univ (fun i : idx => (G i i).re) =
      Finset.prod Finset.univ (fun i : idx =>
        Finset.sum Finset.univ (fun j : idx => norm (A j i) ^ 2)) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [G, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Complex.conj_mul']
    have hp := Complex.ofReal_pow (norm (A j i)) 2
    simpa only [Complex.ofReal_re] using congrArg Complex.re hp.symm
  rw [hd] at h
  exact h
