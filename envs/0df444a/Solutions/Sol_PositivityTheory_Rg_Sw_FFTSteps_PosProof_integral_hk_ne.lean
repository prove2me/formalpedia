-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.integral_hk_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:26.359865+00:00
-- url     : https://prove2.me/submissions/567de8fb-99c9-42e6-8bc6-e9ed9cf10bef

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (k l : ℕ) (h : k ≠ l) : ∫ z, hk k l z = 0 := by
  have hkl : ((k : ℂ) - l) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  set θ : ℝ := Real.pi / ((k : ℝ) - l) with hθ
  have hfac : Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l = -1 := by
    have hs : star (Complex.exp (θ * I)) = Complex.exp (-(θ * I)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      simp
    rw [hs, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have h2 : (θ : ℂ) * ((k : ℂ) - l) = Real.pi := by
      rw [hθ]
      push_cast
      field_simp
    have h3 : (k : ℂ) * (θ * I) + l * (-(θ * I)) = Real.pi * I := by
      linear_combination I * h2
    rw [h3, Complex.exp_pi_mul_I]
  have hrot : ∀ z : ℂ, hk k l (Complex.exp (θ * I) * z) = -hk k l z := by
    intro z
    have he : e1 (Complex.exp (θ * I) * z) = e1 z := by
      simp only [e1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp only [hk]
    rw [he, star_mul', mul_pow, mul_pow]
    calc Complex.exp (θ * I) ^ k * z ^ k * (star (Complex.exp (θ * I)) ^ l * star z ^ l) * e1 z
        = (Complex.exp (θ * I) ^ k * star (Complex.exp (θ * I)) ^ l) * (z ^ k * star z ^ l * e1 z) := by ring
      _ = -(z ^ k * star z ^ l * e1 z) := by rw [hfac]; ring
  have key := (rotation (Circle.exp θ)).measurePreserving.integral_comp
    (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding (hk k l)
  simp only [LinearIsometryEquiv.coe_toHomeomorph, rotation_apply, Circle.coe_exp, hrot, integral_neg] at key
  linear_combination (-1 / 2 : ℂ) * key
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
