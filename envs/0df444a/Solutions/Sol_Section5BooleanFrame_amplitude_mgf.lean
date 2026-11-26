-- Prove2me | solution 1 for Section5BooleanFrame.amplitude_mgf
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:07:33.203802+00:00
-- url     : https://prove2.me/submissions/fdca1b41-ec7e-4391-945c-945c88b19211

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (u : ι → ℝ) (t : ℝ) :
    Section5BooleanFrame.average (fun x => Real.exp (t*Section5BooleanFrame.amplitude u x))=∏ i, Real.cosh (t*u i) := by
  have hexp (x : ι → Bool) : Real.exp (t*Section5BooleanFrame.amplitude u x)=
      ∏ i, Real.exp (t*u i*Section5BooleanFrame.sign x i) := by
    simp only [Section5BooleanFrame.amplitude,Finset.mul_sum,Real.exp_sum,mul_assoc]
  have hsum : (∑ x : ι → Bool, ∏ i, Real.exp (t*u i*Section5BooleanFrame.sign x i))=
      ∏ i, (2*Real.cosh (t*u i)) := by
    simp only [Section5BooleanFrame.sign]
    rw [← Fintype.prod_sum (fun i : ι => fun b : Bool => Real.exp (t*u i*(if b then -1 else 1)))]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true,mul_one,mul_neg_one]
    rw [Real.cosh_eq]
    ring
  simp only [Section5BooleanFrame.average,hexp,hsum,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  have hc : (Fintype.card (ι → Bool) : ℝ)=(2 : ℝ)^Fintype.card ι := by simp
  rw [hc,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)),one_mul]
