-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.integral_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:57.601985+00:00
-- url     : https://prove2.me/submissions/7164047c-4337-4e75-ba0f-71139285f832

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Mom1
namespace PositivityTheory.Rg.Sw.LC.Mom1
theorem _root_.solution (c : ℝ) (p q : ℕ) (hpq : p ≠ q) :
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) = 0 := by
  set F : ℂ → ℂ := fun z => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) with hF
  set f : ℝ → ℂ := fun r => (r : ℂ) ^ (p + q + 1) * Complex.exp ((-(c * r ^ 2) : ℝ)) with hf
  set k : ℂ := ((p : ℂ) - q) * Complex.I with hk
  set g : ℝ → ℂ := fun θ => Complex.exp (k * θ) with hg
  have hk0 : k ≠ 0 := by
    rw [hk]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    rw [sub_ne_zero]
    exact_mod_cast hpq
  have hpt : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π, x.1 • F (Complex.polarCoord.symm x) = f x.1 * g x.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [mem_Ioi] at hr
    have he : ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I = Complex.exp (θ * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    simp only [hF, hf, hg, hk]
    rw [hn, Complex.polarCoord_symm_apply]
    simp only
    rw [he, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
      mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hc : (starRingEnd ℂ) ((θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    rw [hc]
    have : Complex.exp (↑p * (↑θ * Complex.I)) * Complex.exp (↑q * -(↑θ * Complex.I)) =
        Complex.exp (((p : ℂ) - q) * Complex.I * θ) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc (r : ℂ) * ((r : ℂ) ^ p * Complex.exp (↑p * (↑θ * Complex.I)) *
            ((r : ℂ) ^ q * Complex.exp (↑q * -(↑θ * Complex.I))) * Complex.exp ((-(c * r ^ 2) : ℝ)))
        = (r : ℂ) ^ (p + q + 1) * Complex.exp ((-(c * r ^ 2) : ℝ)) *
            (Complex.exp (↑p * (↑θ * Complex.I)) * Complex.exp (↑q * -(↑θ * Complex.I))) := by ring
      _ = _ := by rw [this]
  have hgI : ∫ θ in Ioo (-π) π, g θ = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      hg]
    simp only
    rw [integral_exp_mul_complex hk0]
    have : k * (π : ℂ) = k * ((-π : ℝ) : ℂ) + (((p : ℤ) - q : ℤ) : ℂ) * (2 * π * Complex.I) := by
      rw [hk]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, sub_self, zero_div]
  rw [← Complex.integral_comp_polarCoord_symm F, polarCoord_target,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpt, Measure.volume_eq_prod,
    setIntegral_prod_mul f g, hgI, mul_zero]
end PositivityTheory.Rg.Sw.LC.Mom1
