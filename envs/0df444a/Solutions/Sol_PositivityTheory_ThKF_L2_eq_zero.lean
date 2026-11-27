-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:58.410044+00:00
-- url     : https://prove2.me/submissions/d93253aa-d4bb-4124-be2c-dd7dd720ad76

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
omit [μ.IsMulRightInvariant]
namespace PositivityTheory.ThKF.L2
theorem _root_.solution (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hc : Continuous f) (hf : Inv Γ f)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (h0 : ∫ x in 𝓕, conj (f x) * f x ∂μ = 0) : f = 0 := by
  have e : ∫ x in 𝓕, conj (f x) * f x ∂μ = ((∫ x in 𝓕, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  rw [e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun x => by positivity) f2] at h0
  have hm : MeasurableSet {x | f x ≠ 0} := (isOpen_ne_fun hc continuous_const).measurableSet
  have h1 : μ ({x | f x ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hm]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h0)
    simpa using hx
  have h2 : μ {x | f x ≠ 0} = 0 := h.measure_zero_of_invariant _ (fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change f ((γ⁻¹ : Γ) * x) ≠ 0 ↔ f x ≠ 0
    rw [hf _ (γ⁻¹).2]) h1
  have h3 := (isOpen_ne_fun hc continuous_const).eq_empty_of_measure_zero h2
  funext x
  by_contra hx
  exact (h3 ▸ hx : x ∈ (∅ : Set G))
end PositivityTheory.ThKF.L2
