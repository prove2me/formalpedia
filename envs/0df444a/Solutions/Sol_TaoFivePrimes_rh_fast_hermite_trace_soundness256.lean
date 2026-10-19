-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_hermite_trace_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:44:14.599392+00:00
-- url     : https://prove2.me/submissions/be88b76b-844b-428e-b327-2fb276e5946e

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_scaled_hermite_algebra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastHermiteTrace256Proof
open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256
lemma checked (p:Ball) (x:ℝ) (hp:encloses D p (((5/64:ℝ)*x:ℝ):ℂ)) (hs:List Ball)
 (h0:entry hs 0=integer D 1) (h1:entry hs 1=p)
 (hstep:∀n:Nat,n<50→entry hs (n+2)=hermiteStep p n (entry hs n) (entry hs (n+1))) :
 ∀n:Nat,n≤51→encloses D (entry hs n) ((RHFastGaussianWindow.scaledHermite n x:ℝ):ℂ) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D (by norm_num [D])
 intro n
 induction n using Nat.twoStepInduction with
 | zero=>
  intro hn
  rw [h0]
  simpa [RHFastGaussianWindow.scaledHermite,Polynomial.hermite_zero] using S.integer_mem 1
 | one=>
  intro hn
  rw [h1]
  simpa [RHFastGaussianWindow.scaledHermite,Polynomial.hermite_one] using hp
 | more n ih0 ih1=>
  intro hn
  have hlt:n<50:=by omega
  rw [hstep n hlt,hermiteStep]
  have hc:=S.rational_mem (((n+1)*25:Nat):Int) 4096 (by norm_num)
  have h:=S.sub_mem _ _ _ _ (S.mul_mem _ _ _ _ hp (ih1 (by omega)))
   (S.mul_mem _ _ _ _ hc (ih0 (by omega)))
  convert! h using 1
  rw [(TaoFivePrimes.rh_fast_scaled_hermite_algebra n x).2]
  push_cast
  ring
end RHFastHermiteTrace256Proof

theorem solution (p:RHFastBallArithmetic.Ball) (x:ℝ)
 (hp:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D p (((5/64:ℝ)*x:ℝ):ℂ))
 (hs:List RHFastBallArithmetic.Ball)
 (h0:RHFastBallFrequencyChecker256.entry hs 0=RHFastBallArithmetic.integer RHFastBallFrequencyChecker256.D 1)
 (h1:RHFastBallFrequencyChecker256.entry hs 1=p)
 (hstep:∀n:Nat,n<50→RHFastBallFrequencyChecker256.entry hs (n+2)=
  RHFastBallFrequencyChecker256.hermiteStep p n (RHFastBallFrequencyChecker256.entry hs n) (RHFastBallFrequencyChecker256.entry hs (n+1))) :
 ∀n:Nat,n≤51→RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D (RHFastBallFrequencyChecker256.entry hs n)
  ((RHFastGaussianWindow.scaledHermite n x:ℝ):ℂ) := RHFastHermiteTrace256Proof.checked p x hp hs h0 h1 hstep
#print axioms solution
