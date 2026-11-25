-- Prove2me | solution 1 for PositivityTheory.ThKCT.Unf.cross_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:05.837996+00:00
-- url     : https://prove2.me/submissions/63b854bf-ddde-4702-b1bf-a8e2daab1675

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact
import Theorems.Thm_PositivityTheory_ThKCT_Unf_conv_eq
import Theorems.Thm_PositivityTheory_ThKCT_Unf_cont_M

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
    (hKc : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) {f f₀ : G → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) (h0 : 0 ≤ f) (hf₀ : Continuous f₀) (hs₀ : HasCompactSupport f₀) (h0₀ : 0 ≤ f₀) :
    (∫⁻ g, ENNReal.ofReal (f g) ∂ν) * ∫⁻ g, ENNReal.ofReal (f₀ g) ∂m ≤
      (∫⁻ g, ENNReal.ofReal (f₀ g) ∂ν) * ∫⁻ g, ENNReal.ofReal (f g) ∂m := by
  by_contra hlt
  rw [not_le] at hlt
  have fin : ∀ {φ : G → ℝ}, Continuous φ → HasCompactSupport φ → ∫⁻ g, ENNReal.ofReal (φ g) ∂ν ≠ ⊤ := fun h1 h2 =>
    (h1.integrable_of_hasCompactSupport h2).lintegral_lt_top.ne
  set A := ∫⁻ g, ENNReal.ofReal (f₀ g) ∂ν with hA
  set B := ∫⁻ g, ENNReal.ofReal (f g) ∂ν with hB
  let u : G → ℝ≥0∞ := fun g => A * ∫⁻ x, ENNReal.ofReal (f (x * g)) ∂m
  let v : G → ℝ≥0∞ := fun g => B * ∫⁻ x, ENNReal.ofReal (f₀ (x * g)) ∂m
  have hu : Continuous u := (ENNReal.continuous_const_mul (fin hf₀ hs₀)).comp (cont_M m hf hs h0)
  have hv : Continuous v := (ENNReal.continuous_const_mul (fin hf hs)).comp (cont_M m hf₀ hs₀ h0₀)
  have inv : ∀ {φ : G → ℝ}, Continuous φ → ∀ k ∈ K, ∫⁻ x, ENNReal.ofReal (φ (x * k)) ∂m = ∫⁻ x, ENNReal.ofReal (φ x) ∂m :=
    fun h1 k hk => by
      conv_rhs => rw [← hK k hk]
      rw [lintegral_map (by fun_prop) (measurable_mul_const k)]
  obtain ⟨V, hV, hVK⟩ := compact_open_separated_mul_left hKc (isOpen_lt hu hv) fun k hk => by
    simpa only [u, v, mem_setOf_eq, inv hf k hk, inv hf₀ k hk] using hlt
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  set W := interior (V ∩ C) * (K : Set G) with hW
  have hWo : IsOpen W := isOpen_interior.mul_right
  have hWK : ∀ g, ∀ k ∈ K, g * k ∈ W ↔ g ∈ W := fun g k hk => by
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), by simp only at e ⊢; rw [← mul_assoc, e, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, (mul_assoc _ _ _).symm⟩
  have hb : Measurable (W.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hWo.measurableSet
  have hbK : ∀ g, ∀ k ∈ K, W.indicator (1 : G → ℝ≥0∞) (g * k) = W.indicator 1 g := fun g k hk => by
    by_cases h : g ∈ W <;> simp [h, hWK g k hk]
  have key : ∀ {φ : G → ℝ}, Continuous φ → ∫⁻ g in W, ∫⁻ x, ENNReal.ofReal (φ (x * g)) ∂m ∂ν =
      (∫⁻ x, W.indicator 1 x⁻¹ ∂m) * ∫⁻ g, ENNReal.ofReal (φ g) ∂ν := fun {φ} h1 => by
    rw [← conv_eq ν m hP hPK (f := fun g => ENNReal.ofReal (φ g)) (by fun_prop) hb hbK, ← lintegral_indicator hWo.measurableSet]
    refine lintegral_congr fun g => ?_
    by_cases h : g ∈ W <;> simp [h]
  have hfin : ∫⁻ x, W.indicator 1 x⁻¹ ∂m ≠ ⊤ := by
    have : ∫⁻ x, W.indicator 1 x⁻¹ ∂m = m W⁻¹ := by
      rw [← lintegral_indicator_one hWo.inv.measurableSet]; rfl
    rw [this]
    exact ((measure_mono (inv_subset_inv.2 (mul_subset_mul_right (interior_subset.trans inter_subset_right)))).trans_lt
      (hC.mul hKc).inv.measure_lt_top).ne
  have e1 : ∫⁻ g in W, u g ∂ν = A * ((∫⁻ x, W.indicator 1 x⁻¹ ∂m) * B) := by
    rw [lintegral_const_mul _ (cont_M m hf hs h0).measurable, key hf]
  have e2 : ∫⁻ g in W, v g ∂ν = B * ((∫⁻ x, W.indicator 1 x⁻¹ ∂m) * A) := by
    rw [lintegral_const_mul _ (cont_M m hf₀ hs₀ h0₀).measurable, key hf₀]
  have h3 := setLIntegral_strict_mono (μ := ν) (f := u) (g := v) hWo.measurableSet
    (hWo.measure_ne_zero ν ⟨1 * 1, mul_mem_mul (mem_interior_iff_mem_nhds.2 (Filter.inter_mem hV hC1)) K.one_mem⟩)
    hv.measurable (by rw [e1]; exact ENNReal.mul_ne_top (fin hf₀ hs₀) (ENNReal.mul_ne_top hfin (fin hf hs)))
    (ae_of_all _ fun x hx => hVK (mul_subset_mul_right (interior_subset.trans inter_subset_left) hx))
  rw [e1, e2] at h3
  exact h3.ne (by ring)
end PositivityTheory.ThKCT.Unf
