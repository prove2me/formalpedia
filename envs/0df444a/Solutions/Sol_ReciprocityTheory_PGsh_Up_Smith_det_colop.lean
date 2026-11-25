-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.det_colop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:46.776238+00:00
-- url     : https://prove2.me/submissions/d5ed2b38-921a-4379-9aa9-91b847ecc4d3

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution {b : ℕ} (X : Matrix (Fin (b + 1)) (Fin (b + 1)) R) (j0 : Fin (b + 1))
    (s : Fin (b + 1) → R) :
    (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0).det = X.det := by
  set V : Matrix (Fin (b + 1)) (Fin (b + 1)) R := Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))
    with hV
  have hXV : (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0) = X * V := by
    ext i l
    simp only [Matrix.of_apply, Matrix.mul_apply, hV]
    by_cases hl : l = j0
    · simp [hl]
    · simp only [hl, if_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
  have hV1 : V.det = 1 := by
    rw [Matrix.det_succ_column V j0, Finset.sum_eq_single j0]
    · have hsub : V.submatrix j0.succAbove j0.succAbove = 1 := by
        ext k l
        simp only [Matrix.submatrix_apply, hV, Matrix.of_apply, Fin.succAbove_ne, if_false,
          sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
      rw [hsub, Matrix.det_one]
      simp [hV, ← two_mul, pow_mul]
    · intro k _ hk
      simp [hV, hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hXV, Matrix.det_mul, hV1, mul_one]
end ReciprocityTheory.PGsh.Up.Smith
