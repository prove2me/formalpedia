-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat16_continuous_log_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:42:35.852596+00:00
-- url     : https://prove2.me/submissions/b0f14ed3-16d6-4cf6-a72d-11da6dda0c15

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped Real

theorem solution {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (h0 : f 0 = g 0)
    (h : ∀ ξ, Complex.exp (f ξ) = Complex.exp (g ξ)) : f = g := by
  have hone : ∀ ξ, Complex.exp (f ξ - g ξ) = 1 := fun ξ => by
    rw [Complex.exp_sub, h ξ, div_self (Complex.exp_ne_zero _)]
  have hex : ∀ ξ, ∃ n : ℤ, f ξ - g ξ = n * (2 * ↑π * Complex.I) :=
    fun ξ => Complex.exp_eq_one_iff.mp (hone ξ)
  choose m hm using hex
  have hcast : ∀ ξ, ((m ξ : ℤ) : ℝ) = ((f ξ - g ξ) / (2 * ↑π * Complex.I)).re := by
    intro ξ
    have hquot : (f ξ - g ξ) / (2 * ↑π * Complex.I) = (m ξ : ℂ) := by
      rw [hm ξ, mul_div_assoc, div_self Complex.two_pi_I_ne_zero, mul_one]
    rw [hquot, Complex.intCast_re]
  have hcont_cast : Continuous fun ξ => ((m ξ : ℤ) : ℝ) := by
    simp only [hcast]
    exact Complex.continuous_re.comp ((hf.sub hg).div_const _)
  have hcont_m : Continuous m :=
    Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.mpr hcont_cast
  funext ξ
  have hval : f ξ - g ξ = 0 := by
    rw [hm ξ, PreconnectedSpace.constant (α := ℝ) inferInstance hcont_m (x := ξ) (y := 0),
      ← hm 0, h0, sub_self]
  exact sub_eq_zero.mp hval
