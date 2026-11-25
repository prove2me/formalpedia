-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:04.005315+00:00
-- url     : https://prove2.me/submissions/283e3c79-7346-497e-88bd-2354d01d11f8

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
import Theorems.Thm_P2M_PositivityTheory_ThKEst_CS_Dual_zero__e2e439d12e3f
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_intOn
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_eq_zero
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {P : G → ℂ} (hP : Continuous P)
    (hper : ∀ ξ u, P (r ξ + u) = P u) {c : Γ → ℂ} (hc : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = c ξ)
    (hsum : Summable fun ξ => ‖c ξ‖) : (μ.real D : ℂ) * P 0 = ∑' ξ, c ξ := by
  classical
  set S : G → ℂ := fun u => ∑' ξ, c ξ * e (-ξ) u with hSdef
  have hS : Continuous S := continuous_tsum (fun ξ => continuous_const.mul (h.cont _)) hsum
    (fun ξ u => by simp [h.norm])
  have hSper : ∀ η u, S (r η + u) = S u := fun η u => by simp only [hSdef, h.per]
  have hcoefS : ∀ ξ, ∫ u in D, e ξ u * S u ∂μ = μ.real D * c ξ := by
    intro ξ
    have hsw : ∀ u, e ξ u * S u = ∑' ξ', c ξ' * e (ξ - ξ') u := by
      intro u
      simp only [hSdef, ← tsum_mul_left, sub_eq_add_neg, h.addl]
      exact tsum_congr fun _ => by ring
    simp_rw [hsw]
    have hInt : ∀ ξ', Integrable (fun u => c ξ' * e (ξ - ξ') u) (μ.restrict D) :=
      fun ξ' => h.intOn hD (continuous_const.mul (h.cont _)) fun η u => by rw [h.per]
    have hnorm : ∀ ξ', ∫ u in D, ‖c ξ' * e (ξ - ξ') u‖ ∂μ = μ.real D * ‖c ξ'‖ := by
      intro ξ'
      simp [h.norm]
    rw [← integral_tsum_of_summable_integral_norm hInt (by simp_rw [hnorm]; exact hsum.mul_left _)]
    rw [tsum_eq_single ξ]
    · simp [h.zero]
    · intro ξ' hne
      rw [integral_const_mul, h.orth hD (sub_ne_zero.2 hne.symm), mul_zero]
  have hQ := h.eq_zero hD (P := fun u => (μ.real D : ℂ) * P u - S u) ((continuous_const.mul hP).sub hS)
    (fun ξ u => by simp only [hper, hSper]) fun ξ => by
      have h1 : IntegrableOn (fun u => (μ.real D : ℂ) * (e ξ u * P u)) D μ :=
        h.intOn hD (continuous_const.mul ((h.cont ξ).mul hP)) fun η u => by rw [h.per, hper]
      have h2 : IntegrableOn (fun u => e ξ u * S u) D μ :=
        h.intOn hD ((h.cont ξ).mul hS) fun η u => by rw [h.per, hSper]
      have e1 : ∀ u, e ξ u * ((μ.real D : ℂ) * P u - S u) = (μ.real D : ℂ) * (e ξ u * P u) - e ξ u * S u :=
        fun u => by ring
      simp only [e1]
      rw [integral_sub h1 h2, integral_const_mul, hc, hcoefS, sub_self]
  have := congrFun hQ 0
  simp only [Pi.zero_apply, sub_eq_zero] at this
  rw [this]
  simp [hSdef, h.zero']
end Dual
end PositivityTheory.ThKEst.CS
