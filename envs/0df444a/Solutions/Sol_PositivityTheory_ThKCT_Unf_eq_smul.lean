-- Prove2me | solution 1 for PositivityTheory.ThKCT.Unf.eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:42.052381+00:00
-- url     : https://prove2.me/submissions/22041bf8-2f42-4c95-8a69-ea451819d6ea

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact
import Theorems.Thm_PositivityTheory_ThKCT_Unf_cross_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (ν : Measure G) [ν.IsHaarMeasure] (m : Measure G) [SFinite m] {P : Set G} {K : Subgroup G}
namespace PositivityTheory.ThKCT.Unf
theorem _root_.solution [IsFiniteMeasureOnCompacts m] (hP : ∀ p ∈ P, m.map (p * ·) = m) (hK : ∀ k ∈ K, m.map (· * k) = m)
    (hKc : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ m = c • ν := by
  obtain ⟨⟨f₀, hf₀⟩, hs₀, h0₀, h1⟩ := exists_continuous_nonneg_pos (1 : G)
  have fin : ∀ (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {φ : G → ℝ}, Continuous φ → HasCompactSupport φ →
      ∫⁻ g, ENNReal.ofReal (φ g) ∂μ ≠ ⊤ := fun μ _ _ h1 h2 => (h1.integrable_of_hasCompactSupport h2).lintegral_lt_top.ne
  set A := ∫⁻ g, ENNReal.ofReal (f₀ g) ∂ν with hA
  have hA0 : A ≠ 0 := fun h => by
    have := (lintegral_eq_zero_iff (by fun_prop)).1 h
    have h2 := (Continuous.ae_eq_iff_eq ν (ENNReal.continuous_ofReal.comp hf₀) continuous_zero).1 this
    exact h1 (le_antisymm (ENNReal.ofReal_eq_zero.1 (congrFun h2 1)) (h0₀ 1))
  have hc : (∫⁻ g, ENNReal.ofReal (f₀ g) ∂m) / A ≠ ⊤ := ENNReal.div_ne_top (fin m hf₀ hs₀) hA0
  refine ⟨_, hc, ?_⟩
  lift (∫⁻ g, ENNReal.ofReal (f₀ g) ∂m) / A to ℝ≥0 using hc with c hc'
  rw [← ENNReal.smul_def]
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  have hf : Continuous fun x => (f x : ℝ) := by fun_prop
  have hs : HasCompactSupport fun x => (f x : ℝ) := f.hasCompactSupport.comp_left (g := fun x : ℝ≥0 => (x : ℝ)) rfl
  have h0 : 0 ≤ fun x => (f x : ℝ) := fun x => (f x).2
  have e := le_antisymm (cross_le ν m hP hK hKc hPK hf hs h0 hf₀ hs₀ h0₀) (cross_le ν m hP hK hKc hPK hf₀ hs₀ h0₀ hf hs h0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hf.aestronglyMeasurable, ENNReal.smul_def, lintegral_smul_measure, hc',
    smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, mul_comm (∫⁻ g, ENNReal.ofReal (f₀ g) ∂m)]
  erw [e]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 (fin ν hf₀ hs₀), one_mul]
end PositivityTheory.ThKCT.Unf
