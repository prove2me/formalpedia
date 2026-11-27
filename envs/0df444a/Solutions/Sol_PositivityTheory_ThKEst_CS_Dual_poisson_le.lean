-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.poisson_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:02.871365+00:00
-- url     : https://prove2.me/submissions/f2b9b6ea-188b-4453-ac2f-2a7e3034b6f9

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_lint
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_fin
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_series

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
theorem _root_.solution [LocallyCompactSpace G] (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : G → ℂ, Continuous H →
      (∀ K : Set G, IsCompact K → ∃ b : Γ → ℝ, Summable b ∧ ∀ ξ, ∀ a ∈ K, ‖H (r ξ + a)‖ ≤ b ξ) →
      ‖∑' ξ, H (r ξ)‖ₑ ≤ ENNReal.ofReal c * ∑' ξ, ‖∫ u, e ξ u * H u ∂μ‖ₑ := by
  have hDf := h.fin hD
  have hm : 0 < μ.real D := ENNReal.toReal_pos (hD.measure_ne_zero (NeZero.ne μ)) hDf
  refine ⟨(μ.real D)⁻¹, inv_pos.2 hm, fun H hH hb => ?_⟩
  set c : Γ → ℂ := fun ξ => ∫ u, e ξ u * H u ∂μ with hcdef
  by_cases htop : ∑' ξ, ‖c ξ‖ₑ = ∞
  · rw [htop, ENNReal.mul_top (by simpa using hm)]
    exact le_top
  have hsum : Summable fun ξ => ‖c ξ‖ := by
    have := ENNReal.summable_toReal htop
    simpa using this
  set P : G → ℂ := fun u => ∑' ξ, H (r ξ + u) with hP
  have hper : ∀ ξ u, P (r ξ + u) = P u := by
    intro ξ u
    simp only [hP]
    refine Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => H (r η + u)))
    simp [add_assoc]
  have hT : ∀ ξ, Continuous fun u => H (r ξ + u) := fun ξ => hH.comp (continuous_const.add continuous_id)
  have hPc : Continuous P := by
    rw [continuous_iff_continuousAt]
    intro w
    obtain ⟨N, hN, hNw⟩ := exists_compact_mem_nhds w
    obtain ⟨b, hb1, hb2⟩ := hb N hN
    exact (continuousOn_tsum (fun ξ => (hT ξ).continuousOn) hb1 hb2).continuousAt hNw
  have hfin : ∑' ξ, ∫⁻ u in D, ‖H (r ξ + u)‖ₑ ∂μ ≠ ∞ := by
    obtain ⟨K, hK, hKc⟩ := h.cpt
    obtain ⟨b, hb1, hb2⟩ := hb K hK
    obtain ⟨ξ₀, hξ₀⟩ := hKc 0
    have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => (norm_nonneg _).trans (hb2 ξ _ hξ₀)
    rw [← lintegral_tsum fun ξ => (hT ξ).enorm.measurable.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal (∑' ξ, b ξ) ∂μ) ?_ (lintegral_mono fun u => ?_)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDf
    · obtain ⟨η, hη⟩ := hKc u
      rw [ENNReal.ofReal_tsum_of_nonneg hb0 hb1, ← (Equiv.addRight η).tsum_eq (fun ξ => ENNReal.ofReal (b ξ))]
      refine ENNReal.tsum_le_tsum fun ξ => ?_
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hb2 (ξ + η) _ hη
      rwa [map_add, show r ξ + r η + (u - r η) = r ξ + u by abel] at this
  have hcoef : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = c ξ := by
    intro ξ
    have hgn : ∀ u v, ‖e ξ u * H v‖ₑ = ‖H v‖ₑ := fun u v => by
      rw [← ofReal_norm, ← ofReal_norm, norm_mul, h.norm, one_mul]
    have hgi : Integrable (fun u => e ξ u * H u) μ := by
      refine ⟨((h.cont ξ).mul hH).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      simp only [hgn]
      rw [h.lint hD]
      exact hfin.lt_top
    simp only [hcdef]
    rw [hD.integral_eq_tsum'' _ hgi, ← (AddMonoidHom.ofInjective h.inj).toEquiv.tsum_eq]
    have hv : ∀ η u, ((AddMonoidHom.ofInjective h.inj).toEquiv η +ᵥ u : G) = r η + u := fun η u => rfl
    simp only [hv, h.per, hP, ← tsum_mul_left]
    refine integral_tsum (fun η => ((h.cont ξ).mul (hT η)).aestronglyMeasurable) ?_
    simpa only [hgn] using hfin
  have key := h.series hD hPc hper hcoef hsum
  have h0 : ∑' ξ, H (r ξ) = ((μ.real D)⁻¹ : ℝ) * ∑' ξ, c ξ := by
    rw [← key, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne']
    simp [hP]
  rw [h0, enorm_mul]
  refine mul_le_mul' (le_of_eq ?_) (enorm_tsum_le_tsum_enorm)
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hm).le]
end Dual
end PositivityTheory.ThKEst.CS
