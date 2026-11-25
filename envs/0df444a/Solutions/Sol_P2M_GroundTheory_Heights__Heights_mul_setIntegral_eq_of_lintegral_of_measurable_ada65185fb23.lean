-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_of_measurable_ada65185fb23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:28.150262+00:00
-- url     : https://prove2.me/submissions/eb291fbc-0810-44a8-b73a-8fd857679538

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_integral_smul_mul_eq_toReal_sub_3372cbe3807f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder
variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace X]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {μ : Measure E} {ν : Measure X} {C : Set E}
    {fib : X → Set W} (hfin : ∀ x, (fib x).Finite) (v : X → W → E) (ρ : X → W → ℂ → ℝ)
    (hρ : ∀ x w t, 0 ≤ ρ x w t) (hρc : ∀ x w, Continuous (ρ x w))
    {c : ℝ} (hc : 0 ≤ c) {b : ℝ≥0∞} (hb : b ≠ 0)
    (hA : ∀ F : E → ℝ≥0∞, Measurable F →
      AEMeasurable (fun x => ∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ν ∧
      ENNReal.ofReal c * ∫⁻ y in C, F y ∂μ =
        b * ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ∂ν)
    {f : E → ℝ} (hfm : Measurable f) (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by
  obtain ⟨hGpm, hAp⟩ := hA (fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hfm)
  obtain ⟨hGmm, hAm⟩ := hA (fun y => ENNReal.ofReal (-f y))
    (ENNReal.measurable_ofReal.comp hfm.neg)
  have hCp : ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hf.2).ne
  have hCm : ∫⁻ y in C, ENNReal.ofReal (-f y) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hf.neg.2).ne
  have hIp : ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v x w)) *
      ENNReal.ofReal (ρ x w t)) ∂ν ≠ ⊤ := by
    have h1 : ENNReal.ofReal c * ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCp
    rw [hAp] at h1
    exact fun h2 => h1 (by rw [h2, ENNReal.mul_top hb])
  have hIm : ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v x w)) *
      ENNReal.ofReal (ρ x w t)) ∂ν ≠ ⊤ := by
    have h1 : ENNReal.ofReal c * ∫⁻ y in C, ENNReal.ofReal (-f y) ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCm
    rw [hAm] at h1
    exact fun h2 => h1 (by rw [h2, ENNReal.mul_top hb])
  have hae : (fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) =ᵐ[ν] fun x =>
      (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v x w)) * ENNReal.ofReal (ρ x w t)).toReal -
        (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v x w)) *
          ENNReal.ofReal (ρ x w t)).toReal := by
    filter_upwards [ae_lt_top' hGpm hIp, ae_lt_top' hGmm hIm] with x hxp hxm
    exact finsum_integral_smul_mul_eq_toReal_sub hfm (hfin x) (v x) (ρ x) (hρ x) (hρc x)
      hxp.ne hxm.ne
  rw [integral_congr_ae hae, integral_sub (integrable_toReal_of_lintegral_ne_top hGpm hIp)
    (integrable_toReal_of_lintegral_ne_top hGmm hIm), integral_toReal hGpm (ae_lt_top' hGpm hIp),
    integral_toReal hGmm (ae_lt_top' hGmm hIm), integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    mul_sub, ← ENNReal.toReal_ofReal_mul c _ hc, ← ENNReal.toReal_ofReal_mul c _ hc, hAp, hAm,
    ENNReal.toReal_mul, ENNReal.toReal_mul, mul_sub]
end GroundTheory.Heights₂.Heights
