-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_scaled_gamma_approximation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T12:25:36.904858+00:00
-- url     : https://prove2.me/submissions/dfce2203-897c-49e2-ab44-b5d380c6e40e

import Theorems.Thm_TaoFivePrimes_rh_high_height_complex_stirling
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHHighScaledApproximation
open Complex
noncomputable def approximant (t : ℝ) : ℂ :=
  let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
  Complex.exp ((z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z))
lemma error_le (t : ℝ) (ht : 2≤t) :
    ‖(Complex.Gamma (1/4+((t/2:ℝ):ℂ)*Complex.I)-approximant t)*
      (Real.exp (Real.pi*t/4):ℂ)‖≤96/t^3 := by
  let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
  have hz : 0<z.re := by norm_num [z]
  have hb : 1≤z.im := by simp [z];linarith
  have he := TaoFivePrimes.rh_high_height_complex_stirling.2 z hz hb
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 (t/2)
  have hg' : ‖Complex.Gamma z‖*Real.exp (Real.pi*t/4)≤6 := by
    convert hg using 1 <;> dsimp [z] <;> congr 1 <;> ring
  have him : z.im=t/2 := by simp [z]
  change ‖(Complex.Gamma z-approximant t)*(Real.exp (Real.pi*t/4):ℂ)‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (2*‖Complex.Gamma z‖/z.im^3)*Real.exp (Real.pi*t/4) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = 2*(‖Complex.Gamma z‖*Real.exp (Real.pi*t/4))/(t/2)^3 := by rw [him];ring
    _ ≤ 2*6/(t/2)^3 := by gcongr
    _ = 96/t^3 := by ring
lemma high_error_le (t : ℝ) (ht : 3289999872≤t) :
    ‖(Complex.Gamma (1/4+((t/2:ℝ):ℂ)*Complex.I)-approximant t)*
      (Real.exp (Real.pi*t/4):ℂ)‖≤1/10^25 := by
  apply (error_le t (by linarith)).trans
  have htp : 0<t := by linarith
  have he : (96:ℝ)/(3289999872:ℝ)^3≤1/10^25 := by norm_num
  apply le_trans _ he
  gcongr
end RHHighScaledApproximation

theorem solution :
  (∀ (t : ℝ), 2≤t →
    let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
    ‖(Complex.Gamma z-
      Complex.exp ((z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z)))*
      (Real.exp (Real.pi*t/4):ℂ)‖≤96/t^3) ∧
  (∀ (t : ℝ), 3289999872≤t →
    let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
    ‖(Complex.Gamma z-
      Complex.exp ((z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z)))*
      (Real.exp (Real.pi*t/4):ℂ)‖≤1/10^25) := ⟨RHHighScaledApproximation.error_le,RHHighScaledApproximation.high_error_le⟩
