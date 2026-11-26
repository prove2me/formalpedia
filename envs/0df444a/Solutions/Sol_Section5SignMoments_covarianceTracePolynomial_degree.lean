-- Prove2me | solution 1 for Section5SignMoments.covarianceTracePolynomial_degree
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:03.312725+00:00
-- url     : https://prove2.me/submissions/5e4018e6-0f49-4ed9-aac7-232ff85d0f61

import Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
import Mathlib
section
set_option autoImplicit false

namespace Section5SignMoments

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

theorem matrix_power_degree (A : Matrix ι ι (MvPolynomial σ ℝ)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) (p : ℕ) (i j : ι) :
    ((A^p) i j).totalDegree ≤ p*d := by
  induction p generalizing i j with
  | zero =>
    simp only [pow_zero,Matrix.one_apply,zero_mul]
    split <;> simp
  | succ p ih =>
    rw [pow_succ,Matrix.mul_apply]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    calc
      _ ≤ ((A^p) i l).totalDegree+(A l j).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ p*d+d := Nat.add_le_add (ih i l) (hA l j)
      _ = _ := by ring





theorem covariancePolynomial_degree (S : Matrix ι ι ℝ) (i j : ι) :
    (covariancePolynomial (J := J) S i j).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub_C_le _ _).trans
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C,zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  simpa using MvPolynomial.totalDegree_mul
    (MvPolynomial.X (r,i) : MvPolynomial (J × ι) ℝ) (MvPolynomial.X (r,j))









end Section5SignMoments

end
set_option autoImplicit false
namespace Section5SignMoments
end Section5SignMoments
open Section5SignMoments
variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
theorem solution (S : Matrix ι ι ℝ) (p : ℕ) :
    (Section5SignMoments.covarianceTracePolynomial (J := J) S p).totalDegree ≤ 4*p := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  have he := Section5SignMoments.matrix_power_degree (Section5SignMoments.covariancePolynomial (J := J) S) 2
    (Section5SignMoments.covariancePolynomial_degree S) (2*p) i i
  simpa only [Matrix.diag_apply,show 2*p*2=4*p by omega] using he
