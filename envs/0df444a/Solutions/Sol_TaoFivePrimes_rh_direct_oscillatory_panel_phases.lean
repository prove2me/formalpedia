-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_oscillatory_panel_phases
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:31:01.298173+00:00
-- url     : https://prove2.me/submissions/383c1584-f977-43e0-9708-9a29a49305ea

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset

namespace DirectPhasePanels

lemma seed_error (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - ∑ m ∈ Finset.range 128, z^m/(m.factorial:ℂ)‖ ≤ 1/10^214 := by
  have h := Complex.exp_bound hz (n:=128) (by norm_num)
  have hp : ‖z‖^128 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  calc
    _ ≤ ‖z‖^128 * ((129:ℝ) * (((128:ℕ).factorial * 128:ℕ):ℝ)⁻¹) := by
      simpa using h
    _ ≤ (129:ℝ) * (((128:ℕ).factorial * 128:ℕ):ℝ)⁻¹ := by
      nlinarith [inv_nonneg.mpr (show (0:ℝ) ≤ (((128:ℕ).factorial * 128:ℕ):ℝ) by positivity)]
    _ ≤ 1/10^214 := by norm_num [Nat.factorial]

lemma power_error (a b : ℂ) (ha : ‖a‖ = 1) (ε : ℝ) (hε : 0≤ε)
    (hab : ‖a-b‖≤ε) (n : ℕ) :
    ‖a^n-b^n‖ ≤ n*ε*(1+ε)^n := by
  have hb : ‖b‖≤1+ε := by
    have h := norm_add_le (b-a) a
    rw [sub_add_cancel,ha,norm_sub_rev] at h
    linarith
  have hp : ∀ k : ℕ, 1≤(1+ε)^k := by
    intro k
    exact one_le_pow₀ (by linarith) 
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : a^(n+1)-b^(n+1) = (a^n-b^n)*b+a^n*(a-b) := by
      rw [pow_succ,pow_succ]
      ring
    rw [hid]
    have hnorm : ‖a^n‖=1 := by rw [norm_pow,ha,one_pow]
    have h1 : ‖(a^n-b^n)*b‖ ≤ (n*ε*(1+ε)^n)*(1+ε) := by
      rw [norm_mul]
      exact mul_le_mul ih hb (norm_nonneg _) (by positivity)
    have h2 : ‖a^n*(a-b)‖≤ε := by
      rw [norm_mul,hnorm,one_mul]
      exact hab
    have h3 : ε ≤ ε*(1+ε)^(n+1) := by
      nlinarith [hp (n+1)]
    calc
      _ ≤ ‖(a^n-b^n)*b‖+‖a^n*(a-b)‖ := norm_add_le _ _
      _ ≤ (n*ε*(1+ε)^n)*(1+ε)+ε := add_le_add h1 h2
      _ ≤ ((n+1:ℕ):ℝ)*ε*(1+ε)^(n+1) := by
        have h3' : ε ≤ ε*((1+ε)^n*(1+ε)) := by simpa [pow_succ] using h3
        calc
          _ ≤ (n:ℝ)*ε*(1+ε)^n*(1+ε)+ε*((1+ε)^n*(1+ε)) := by
            linarith
          _ = _ := by rw [pow_succ]; push_cast; ring

end DirectPhasePanels

/-- A single rational Taylor seed approximates all sixteen panel phases.
For rational frequency the polynomial and its powers have rational real and
imaginary parts; the statement does not claim a particular rounding. -/
theorem solution (τ : ℝ) (hτ : |τ|≤100) (i : ℕ) (hi : i<16) :
    ‖Complex.exp (Complex.I*(τ:ℂ)*(3*(2*(i:ℂ)+1)/16)) -
      (∑ m ∈ Finset.range 128,
        (Complex.I*((3*τ/512:ℝ):ℂ))^m/(m.factorial:ℂ))^(32*(2*i+1))‖ ≤ 1/10^210 := by
  let x : ℂ := Complex.I*((3*τ/512:ℝ):ℂ)
  let q : ℂ := ∑ m ∈ Finset.range 128, x^m/(m.factorial:ℂ)
  let n : ℕ := 32*(2*i+1)
  let ε : ℝ := 1/10^214
  have hx : ‖x‖≤1 := by
    simp only [x,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<512),
      abs_of_pos (by norm_num : (0:ℝ)<3)]
    linarith
  have he : ‖Complex.exp x-q‖≤ε := DirectPhasePanels.seed_error x hx
  have ha : ‖Complex.exp x‖=1 := by simp [x,Complex.norm_exp,Complex.mul_re]
  have hn : n≤992 := by dsimp [n]; omega
  have he0 : 0≤ε := by positivity
  have hnε : (n:ℝ)*ε≤1 := by
    have hnR : (n:ℝ)≤992 := by exact_mod_cast hn
    dsimp [ε]
    nlinarith
  have hpow : (1+ε)^n ≤ 3 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+ε)
      (by simpa [add_comm] using Real.add_one_le_exp ε) n
    rw [← Real.exp_nat_mul] at h
    exact h.trans ((Real.exp_le_exp.mpr hnε).trans (le_of_lt (by linarith [Real.exp_one_lt_d9])))
  have hp := DirectPhasePanels.power_error (Complex.exp x) q ha ε he0 he n
  have hq : ‖(Complex.exp x)^n-q^n‖ ≤ 1/10^210 := by
    apply hp.trans
    have hnR : (n:ℝ)≤992 := by exact_mod_cast hn
    dsimp [ε] at *
    nlinarith
  have hid : Complex.exp (Complex.I*(τ:ℂ)*(3*(2*(i:ℂ)+1)/16)) =
      (Complex.exp x)^n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [x,n]
    push_cast
    ring
  simpa only [hid,q,n,x] using hq
