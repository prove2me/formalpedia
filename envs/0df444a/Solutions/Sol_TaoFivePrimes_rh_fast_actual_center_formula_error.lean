-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_actual_center_formula_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:09:05.618729+00:00
-- url     : https://prove2.me/submissions/2ccfe653-3bca-43c3-83a8-dc0fa123c0ee

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Theorems.Thm_TaoFivePrimes_rh_fast_actual_to_proxy_fourier_error
import Theorems.Thm_TaoFivePrimes_rh_fast_center_polynomial_fourier_formula
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex
open scoped FourierTransform

theorem solution (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (x:ℝ) :
 ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) x-RHFastGaussianWindow.fourierFormula T k x‖≤1/(2*10^15) := by
 have hf:RHHighSamplingFunctions.moment (T:ℝ) k=
  (fun t:ℝ=>Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*I)*
    Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ))*RHFastGaussianWindow.momentFactor k t) := by
  funext t
  simp only [RHHighSamplingFunctions.moment,RHHighSamplingFunctions.gammaWindow,RHFastGaussianWindow.momentFactor]
  rw [add_comm t (T:ℝ)]
  ring
 have h:=TaoFivePrimes.rh_fast_actual_to_proxy_fourier_error T hT hU k x
 rw [(TaoFivePrimes.rh_fast_center_polynomial_fourier_formula T k).2 x,←hf] at h
 exact h
#print axioms solution
