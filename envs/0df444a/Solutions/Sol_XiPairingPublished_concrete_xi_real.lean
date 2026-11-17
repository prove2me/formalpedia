-- Prove2me | solution 1 for XiPairingPublished.concrete_xi_real
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T11:18:15.100506+00:00
-- url     : https://prove2.me/submissions/b23abdc3-1a40-4ee4-9094-5c0aac350268

import Mathlib
open Complex
namespace EtaQBridge
-- This definition includes the removable values at s = 0 and s = 1.
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  have hz := differentiable_completedZeta₀
  unfold xi
  fun_prop

theorem xi_functional_equation (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

theorem xi_centered_even (u : ℂ) : xi (1/2-u) = xi (1/2+u) := by
  convert xi_functional_equation (1/2+u) using 1 <;> congr 1 <;> ring

theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  <;> ring

theorem xi_eq_zeta (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s-1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hr
  field_simp


theorem gamma_real (x : ℝ) :
    Complex.Gammaℝ (x : ℂ) = ((Real.pi ^ (-x/2) * Real.Gamma (x/2) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ, Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le]
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  have h := Complex.Gamma_ofReal (x/2)
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
  rw [h]

theorem xi_real_pos (x : ℝ) (hx : 0 < x) : ((xi (x : ℂ)).re : ℂ) = xi (x : ℂ) := by
  by_cases hx1 : x = 1
  · subst x; norm_num [xi]
  apply Complex.conj_eq_iff_re.mp
  rw [xi_eq_zeta (x : ℂ) (by simpa using hx) (by exact_mod_cast hx1)]
  have hz : (starRingEnd ℂ) (riemannZeta (x : ℂ)) = riemannZeta (x : ℂ) := by
    simpa using (riemannZeta_conj (x : ℂ)).symm
  rw [gamma_real]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp [hz,h2]

theorem xi_real (x : ℝ) : ((xi (x : ℂ)).re : ℂ) = xi (x : ℂ) := by
  by_cases hx : 0 < x
  · exact xi_real_pos x hx
  · have h := xi_real_pos (1-x) (by linarith : 0 < 1-x)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, xi_functional_equation] using h
end EtaQBridge

theorem solution (x : ℝ) :
    (((((1 + (x : ℂ)*((x : ℂ)-1)*completedRiemannZeta₀ (x : ℂ))/2)).re) : ℂ) =
      (1 + (x : ℂ)*((x : ℂ)-1)*completedRiemannZeta₀ (x : ℂ))/2 :=
  EtaQBridge.xi_real x
#print axioms solution
