-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_5f5cb8ed0534
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:01.155084+00:00
-- url     : https://prove2.me/submissions/d80ddc3a-5d53-419b-9a91-2bbb8a1006fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mul_setIntegral_eq_of_lintegral_of_measurable_ada65185fb23

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
    {f : E → ℝ} (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hf.1.ae_eq_mk)
  obtain ⟨hG0m, hA0⟩ := hA (N.indicator 1) (measurable_one.indicator hNm)
  rw [lintegral_indicator_one hNm, hN0, mul_zero, eq_comm, mul_eq_zero, or_iff_right hb,
    lintegral_eq_zero_iff' hG0m] at hA0
  have hae : (fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) =ᵐ[ν]
      fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, hf.1.mk f (t • v x w) * ρ x w t := by
    filter_upwards [hA0] with x hx
    refine finsum_mem_congr rfl fun w hw => integral_congr_ae ?_
    have hx' : ∫⁻ t : ℂ, N.indicator 1 (t • v x w) * ENNReal.ofReal (ρ x w t) = 0 := by
      simp only [Pi.zero_apply, finsum_mem_eq_finite_toFinset_sum _ (hfin x),
        Finset.sum_eq_zero_iff] at hx
      exact hx w ((hfin x).mem_toFinset.2 hw)
    have hm : Measurable fun t : ℂ => N.indicator 1 (t • v x w) * ENNReal.ofReal (ρ x w t) :=
      ((measurable_one.indicator hNm).comp (continuous_id.smul continuous_const).measurable).mul
        (ENNReal.measurable_ofReal.comp (hρc x w).measurable)
    rw [lintegral_eq_zero_iff' hm.aemeasurable] at hx'
    filter_upwards [hx'] with t ht
    rcases mul_eq_zero.1 ht with h | h
    · have hy : t • v x w ∉ N := by
        intro hy
        simp [Set.indicator_of_mem hy] at h
      have : f (t • v x w) = hf.1.mk f (t • v x w) := by
        by_contra hne
        exact hy (hsub hne)
      rw [this]
    · rw [ENNReal.ofReal_eq_zero] at h
      rw [le_antisymm h (hρ x w t), mul_zero, mul_zero]
  rw [integral_congr_ae hf.1.ae_eq_mk, integral_congr_ae hae]
  exact mul_setIntegral_eq_of_lintegral_of_measurable hfin v ρ hρ hρc hc hb hA
    hf.1.stronglyMeasurable_mk.measurable (hf.congr hf.1.ae_eq_mk)
end GroundTheory.Heights₂.Heights
