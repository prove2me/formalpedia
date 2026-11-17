-- Prove2me | solution 1 for XiCountedQPublished.xi_zero_geometry
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:32:24.418165+00:00
-- url     : https://prove2.me/submissions/8e5e7133-9d0c-4fc7-8456-679a8bfbe55a

import Mathlib

set_option maxRecDepth 4000

open scoped BigOperators
open Filter Topology

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


end EtaQBridge

namespace XiZeroGeometry
open EtaQBridge Set

theorem xi_zero_value : xi 0 = 1/2 := by simp [xi]
theorem xi_one_value : xi 1 = 1/2 := by simp [xi]

theorem xi_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, xi_one_value]; norm_num
  have hr : 0 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_zeta s hr h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0
    (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hr))
    (riemannZeta_ne_zero_of_one_le_re hs)) (by norm_num)

theorem xi_ne_zero_left (s : ℂ) (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_functional_equation s]
  apply xi_ne_zero_right
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem xi_zero_iff (s : ℂ) :
    xi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hx
    have hr : 0 < s.re := lt_of_not_ge (fun h => xi_ne_zero_left s h hx)
    have hl : s.re < 1 := lt_of_not_ge (fun h => xi_ne_zero_right s h hx)
    have h0 : s ≠ 0 := by intro h; simp [h] at hr
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1] at hx
    have hz : riemannZeta s = 0 := by
      rcases (div_eq_zero_iff).mp hx with hh | hh
      · exact (mul_eq_zero.mp hh).resolve_left
          (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
            (Complex.Gammaℝ_ne_zero_of_re_pos hr))
      · norm_num at hh
    exact ⟨hz, hr, hl⟩
  · rintro ⟨hz, hr, hl⟩
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1, hz]
    ring

theorem xi_zero_reflection (s : ℂ) : xi (1-s) = 0 ↔ xi s = 0 := by
  rw [xi_functional_equation]

theorem xi_zeros_compact_finite (S : Set ℂ) (hS : IsCompact S) :
    (S ∩ {s | xi s = 0}).Finite := by
  apply hS.inter_riemannZetaZeros_finite.subset
  intro s hs
  exact ⟨hs.1, (xi_zero_iff s).mp hs.2 |>.1⟩

theorem centered_zero_strip (s : ℂ) (hs : xi s = 0) : |s.re - 1/2| < 1/2 := by
  have h := (xi_zero_iff s).mp hs
  rw [abs_lt]
  constructor <;> linarith [h.2.1, h.2.2]

end XiZeroGeometry

namespace XiZeroGeometry
theorem squared_zero_coordinate (s : ℂ) :
    (((s.im^2-(s.re-1/2)^2 : ℝ) : ℂ) -
      ((2*(s.re-1/2)*s.im : ℝ) : ℂ)*Complex.I) = -(s-1/2)^2 := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring
end XiZeroGeometry

theorem solution  :
    (∀ s : ℂ, (1+s*(s-1)*completedRiemannZeta₀ s)/2 = 0 ↔
      riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1) ∧
    (∀ S : Set ℂ, IsCompact S →
      (S ∩ {s | (1+s*(s-1)*completedRiemannZeta₀ s)/2 = 0}).Finite) ∧
    (∀ s : ℂ, (((s.im^2-(s.re-1/2)^2 : ℝ) : ℂ) -
      ((2*(s.re-1/2)*s.im : ℝ) : ℂ)*Complex.I) = -(s-1/2)^2) := by
  exact ⟨XiZeroGeometry.xi_zero_iff, XiZeroGeometry.xi_zeros_compact_finite, XiZeroGeometry.squared_zero_coordinate⟩
