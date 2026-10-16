-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_scaled_hermite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:36:14.531546+00:00
-- url     : https://prove2.me/submissions/9f7bd968-0041-4f6d-b12d-5765336a5f4f

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Polynomial
namespace RHFastScaledHermiteAlgebra
lemma hermite_derivative (n:Nat) :
  Polynomial.derivative (Polynomial.hermite (n+1))=
    Polynomial.C ((n+1:Nat):Int)*Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_one,Polynomial.hermite_zero]
  | succ n ih =>
    rw [Polynomial.hermite_succ (n+1),Polynomial.derivative_sub,
      Polynomial.derivative_mul,Polynomial.derivative_X,one_mul,ih]
    simp only [Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add]
    rw [Polynomial.hermite_succ n]
    simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
    ring

lemma hermite_recurrence (n:Nat) :
 Polynomial.hermite (n+2)=Polynomial.X*Polynomial.hermite (n+1)-
   Polynomial.C ((n+1:Nat):Int)*Polynomial.hermite n := by
 rw [show n+2=(n+1)+1 by omega,Polynomial.hermite_succ,hermite_derivative]


lemma real_eval (n:Nat) (x:ℝ) :
 Polynomial.aeval (x:ℂ) (Polynomial.hermite n)=
   (((Polynomial.hermite n).eval₂ (Int.castRingHom ℝ) x:ℝ):ℂ) := by
 rw [Polynomial.aeval_def]
 have h:=Polynomial.hom_eval₂ (p:=Polynomial.hermite n) (f:=Int.castRingHom ℝ)
   (g:=Complex.ofRealHom) x
 convert! h.symm using 1
lemma scaled_recurrence (n:Nat) (x:ℝ) :
 RHFastGaussianWindow.scaledHermite (n+2) x=
  ((5/64:ℝ)*x)*RHFastGaussianWindow.scaledHermite (n+1) x-
   ((n+1:Nat):ℝ)*(5/64:ℝ)^2*RHFastGaussianWindow.scaledHermite n x := by
 simp only [RHFastGaussianWindow.scaledHermite,hermite_recurrence,
   Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_X,Polynomial.eval₂_C,
   map_natCast,Polynomial.eval₂_natCast]
 simp only [pow_succ]
 ring
end RHFastScaledHermiteAlgebra

theorem solution (n:Nat) (x:ℝ) :
 Polynomial.aeval (x:ℂ) (Polynomial.hermite n)=
   (((Polynomial.hermite n).eval₂ (Int.castRingHom ℝ) x:ℝ):ℂ) ∧
 RHFastGaussianWindow.scaledHermite (n+2) x=
  ((5/64:ℝ)*x)*RHFastGaussianWindow.scaledHermite (n+1) x-
   ((n+1:Nat):ℝ)*(5/64:ℝ)^2*RHFastGaussianWindow.scaledHermite n x :=
 ⟨RHFastScaledHermiteAlgebra.real_eval n x,RHFastScaledHermiteAlgebra.scaled_recurrence n x⟩
#print axioms solution
