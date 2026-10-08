-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.gram_psd_isSumSq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:25:56.875834+00:00
-- url     : https://prove2.me/submissions/e5263328-2e38-4381-96d9-811c663a3e7c

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

open SemialgebraicSDP.Psatz MvPolynomial
open scoped MatrixOrder
set_option maxHeartbeats 2000000

theorem SemialgebraicSDP.Psatz.gram_psd_isSumSq {n d : ℕ}
    (Q : Matrix (Mon n d) (Mon n d) ℝ) (hQ : Q.PosSemidef) :
    IsSumSq (gramPoly Q) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  have he : gramPoly Q =
      ∑ k, (∑ a, C (B k a) * monVec n d a) ^ 2 := by
    rw [hB]
    simp only [gramPoly, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, star_trivial, map_sum, map_mul, pow_two,
      Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1
    funext k
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  exact IsSumSq.sum_sq _ _

theorem solution {n d : ℕ} (Q : Matrix (Mon n d) (Mon n d) ℝ)
    (hQ : Q.PosSemidef) : IsSumSq (gramPoly Q) :=
  SemialgebraicSDP.Psatz.gram_psd_isSumSq Q hQ

#print axioms solution
