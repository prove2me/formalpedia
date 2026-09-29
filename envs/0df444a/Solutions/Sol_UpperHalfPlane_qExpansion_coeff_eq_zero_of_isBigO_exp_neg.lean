-- Prove2me | solution 1 for UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cb6f1def-685f-5fb8-9179-f104e3224a3f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg

set_option autoImplicit false

noncomputable section

namespace DecayVanish

open UpperHalfPlane Filter Asymptotics Function
open scoped Real Topology Manifold

theorem norm_integrand_le (f : ℍ → ℂ) (n : ℕ) {C L t A : ℝ} (ht : 0 < t) (hAt : A ≤ t)
    (hC : ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C * ‖Real.exp (-(2 * Real.pi * L) * z.im)‖) (u : ℝ) :
    ‖1 / Periodic.qParam 1 (u + t * (UpperHalfPlane.I : ℂ)) ^ n *
        f ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩‖ ≤
      max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
  set τ : ℍ := ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩ with hτ
  have hI : (u + t * (UpperHalfPlane.I : ℂ)).im = t := by simp [UpperHalfPlane.I]
  have him : τ.im = t := by rw [hτ]; exact hI
  rw [norm_mul, norm_div, norm_one, norm_pow, Periodic.norm_qParam]
  have h1 : (1 : ℝ) / Real.exp (-2 * Real.pi * (u + t * (UpperHalfPlane.I : ℂ)).im / 1) ^ n =
      Real.exp (2 * Real.pi * n * t) := by
    rw [hI, div_one, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1; ring
  rw [h1]
  have h2 : ‖f τ‖ ≤ max C 0 * Real.exp (-(2 * Real.pi * L) * t) := by
    have := hC τ (him ▸ hAt)
    rw [him, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  calc Real.exp (2 * Real.pi * n * t) * ‖f τ‖
      ≤ Real.exp (2 * Real.pi * n * t) * (max C 0 * Real.exp (-(2 * Real.pi * L) * t)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem main (f : ℍ → ℂ)
    (hper : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (qExpansion 1 f) = 0 := by
  obtain ⟨C, hC⟩ := hO.bound
  rw [Filter.Eventually, atImInfty_mem] at hC
  obtain ⟨A, hA⟩ := hC
  set a : ℂ := PowerSeries.coeff n (qExpansion 1 f) with ha

  have hbound : ∀ t : ℝ, max A 1 ≤ t →
      ‖a‖ ≤ max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t) := by
    intro t hAt
    have ht : 0 < t := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hAt)
    have hint := qExpansion_coeff_eq_intervalIntegral one_pos hper hhol hbdd n ht
    simp only [Complex.ofReal_one, div_one, one_mul] at hint
    rw [ha, hint]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => 1 / Periodic.qParam 1 (u + t * (UpperHalfPlane.I : ℂ)) ^ n *
        f ⟨u + t * (UpperHalfPlane.I : ℂ), by simpa using ht⟩)
      (C := max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t))
      (fun u _ => norm_integrand_le f n ht ((le_max_left A 1).trans hAt) hA u)
    simpa using this

  have hlim : Tendsto (fun t : ℝ => max C 0 * Real.exp (2 * Real.pi * ((n : ℝ) - L) * t))
      atTop (𝓝 0) := by
    have hneg : 2 * Real.pi * ((n : ℝ) - L) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hn)
    have h1 : Tendsto (fun t : ℝ => Real.exp (2 * Real.pi * ((n : ℝ) - L) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
    simpa using h1.const_mul (max C 0)
  have hle : ‖a‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨max A 1, hbound⟩)
  exact norm_le_zero_iff.mp hle

end DecayVanish

end

open UpperHalfPlane in
open scoped Manifold in
theorem solution (f : UpperHalfPlane → ℂ)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) = 0 :=
  DecayVanish.main f hper hhol hbdd L hO n hn

#print axioms solution

end S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg
end P2MW
export P2MW.S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg (solution)
