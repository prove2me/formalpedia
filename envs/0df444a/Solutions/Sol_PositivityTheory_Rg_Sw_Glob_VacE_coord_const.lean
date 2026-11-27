-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.VacE.coord_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:21:00.805311+00:00
-- url     : https://prove2.me/submissions/865e099c-ea6e-40a7-a83f-6d0d0dc9357e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_CoordGamma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacE
namespace PositivityTheory.Rg.Sw.Glob.VacE
theorem _root_.solution (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    ((co⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2)) *
        ((Real.pi : ℂ) / (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) -
          I * t * σ * ((si * co : ℝ) : ℂ))) * (((|t| / Real.pi : ℝ) : ℂ)) ^ 2 =
      co + I * (σ * t / c) * si := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have habs : ((|t| : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs]; exact_mod_cast ht
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC, div_pow, habs]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  have key : (co : ℂ)⁻¹ * ((Real.pi : ℂ) / ((c : ℂ) * (co : ℂ)⁻¹ ^ 2)) *
      ((Real.pi : ℂ) / (co * ((c : ℂ) * co - I * t * σ * si))) * ((c : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) =
      (c : ℂ) / ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [key, div_eq_iff hden]
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  field_simp
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq
end PositivityTheory.Rg.Sw.Glob.VacE
