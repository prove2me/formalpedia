-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_polynomial_algebra
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:17:10.459969+00:00
-- url     : https://prove2.me/submissions/3260b063-1ff3-4630-8d51-0eb368c78ca3

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset Polynomial
namespace RHFastPolynomialAlgebra
open RHFastGaussianWindow
lemma delta_eval (T:Nat) (t:ℝ) :
 (deltaPolynomial T).eval ((t:ℂ)/256)=delta T t := by
 have hu:128*I*((t:ℂ)/256)=((t/2:ℝ):ℂ)*I := by push_cast;ring
 have hlog (v u:ℂ):
  (∑j∈Finset.range 7,((-1:ℂ)^(j+1)/(j:ℂ))*(u*v⁻¹)^j)=Complex.logTaylor 7 (u/v) := by
  unfold Complex.logTaylor
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv]
  ring
 unfold deltaPolynomial
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
  Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_finsetSum,
  Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_neg]
 rw [hu,hlog]
 unfold delta
 simp only [div_eq_mul_inv,neg_mul]
 push_cast
 ring
lemma delta_degree (T:Nat) : (deltaPolynomial T).natDegree≤7 := by
 unfold deltaPolynomial
 simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty]
 compute_degree
lemma proxy_degree (T:Nat) : (proxyPolynomial T).natDegree≤28 := by
 unfold proxyPolynomial
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro r hr
 have hr4:r≤4:=by have :=Finset.mem_range.mp hr;omega
 apply Polynomial.natDegree_mul_le.trans
 simp only [Polynomial.natDegree_C,add_zero]
 exact (Polynomial.natDegree_pow_le_of_le r (delta_degree T)).trans (by omega)
lemma proxy_eval (T:Nat) (t:ℝ) :
 (proxyPolynomial T).eval ((t:ℂ)/256)=exponentialPolynomial (delta T t) := by
 simp only [proxyPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
  Polynomial.eval_pow,Polynomial.eval_C,delta_eval]
 simp only [exponentialPolynomial,div_eq_mul_inv]
end RHFastPolynomialAlgebra

theorem solution (T:Nat) :
 (RHFastGaussianWindow.proxyPolynomial T).natDegree≤28 ∧
 ∀t:ℝ,(RHFastGaussianWindow.proxyPolynomial T).eval ((t:ℂ)/256)=
   RHFastGaussianWindow.exponentialPolynomial (RHFastGaussianWindow.delta T t) :=
 ⟨RHFastPolynomialAlgebra.proxy_degree T,RHFastPolynomialAlgebra.proxy_eval T⟩
#print axioms solution
