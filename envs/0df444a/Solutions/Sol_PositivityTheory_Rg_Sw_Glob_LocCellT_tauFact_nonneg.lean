-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.LocCellT.tauFact_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:30.568043+00:00
-- url     : https://prove2.me/submissions/cfc0aa8c-fd91-43dc-b241-10cd5aca728f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_LocCellT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.LocCellT
variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [IsTopologicalAddGroup X]
namespace PositivityTheory.Rg.Sw.Glob.LocCellT
theorem _root_.solution (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (g : X → ℝ≥0) (hgm : Measurable g)
    (hg : ∀ x u, g (x + s u) = g x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ < ∞) :
    ∃ c : ℝ≥0, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a →
      ∫ z, a (π z) * (g z : ℂ) ∂μ = (c : ℂ) * ∫ u, a u := by
  have hπm : Measurable π := hπ.measurable
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity fun z => (g z : ℝ≥0∞)).map π with hν
  have hlin : ∀ F : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ u, F u ∂ν = ∫⁻ z, (g z : ℝ≥0∞) * F (π z) ∂μ := by
    intro F hF
    rw [hν, lintegral_map hF hπm]
    change ∫⁻ a, (F ∘ π) a ∂(μ.withDensity fun z => (g z : ℝ≥0∞)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hgm.coe_nnreal_ennreal (hF.comp hπm)]
    rfl
  have hshift : ∀ (F : (Fin m → Fin n → ℂ) → ℝ≥0∞), Measurable F → ∀ u,
      ∫⁻ z, (g z : ℝ≥0∞) * F (π z + u) ∂μ = ∫⁻ z, (g z : ℝ≥0∞) * F (π z) ∂μ := by
    intro F hF u
    have h := lintegral_add_right_eq_self (μ := μ) (fun z => (g z : ℝ≥0∞) * F (π z)) (s u)
    simpa only [hπs, hg] using h
  have : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hlin _ (measurable_one.indicator (measurable_const_add u hA)),
      hlin _ (measurable_one.indicator hA)]
    have e : ∀ z, ((fun v => u + v) ⁻¹' A).indicator (1 : (Fin m → Fin n → ℂ) → ℝ≥0∞) (π z) =
        A.indicator 1 (π z + u) := by
      intro z
      by_cases h : π z + u ∈ A
      · have h' : u + π z ∈ A := by rwa [add_comm]
        simp [Set.indicator, h, h']
      · have h' : u + π z ∉ A := by rwa [add_comm]
        simp [Set.indicator, h, h']
    simp_rw [e]
    exact hshift _ (measurable_one.indicator hA) u
  have : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hne hρ.continuousOn
    have hr : 0 < ρ u0 := hρpos u0
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [← lintegral_indicator_one hKm, hlin _ (measurable_one.indicator hKm)]
    calc ∫⁻ z, (g z : ℝ≥0∞) * K.indicator 1 (π z) ∂μ
        ≤ ∫⁻ z, (ENNReal.ofReal (ρ u0))⁻¹ * (ENNReal.ofReal (ρ (π z)) * g z) ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : π z ∈ K
          · have h0 : ENNReal.ofReal (ρ u0) ≠ 0 := by simp [hr]
            have h1 : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z)) :=
              calc (1 : ℝ≥0∞) = (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ u0) :=
                    (ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top).symm
                _ ≤ (ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z)) :=
                    by gcongr; exact hmin hz
            calc (g z : ℝ≥0∞) * K.indicator 1 (π z) = (g z : ℝ≥0∞) * 1 := by
                  rw [Set.indicator_of_mem hz, Pi.one_apply]
              _ ≤ (g z : ℝ≥0∞) * ((ENNReal.ofReal (ρ u0))⁻¹ * ENNReal.ofReal (ρ (π z))) := by gcongr
              _ = (ENNReal.ofReal (ρ u0))⁻¹ * (ENNReal.ofReal (ρ (π z)) * g z) := by ring
          · simp [Set.indicator_of_notMem hz]
      _ = (ENNReal.ofReal (ρ u0))⁻¹ * ∫⁻ z, ENNReal.ofReal (ρ (π z)) * g z ∂μ := by
          rw [lintegral_const_mul']
          simp [hr]
      _ < ∞ := ENNReal.mul_lt_top (by simp [hr]) hint
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν = c • (volume : Measure (Fin m → Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  refine ⟨c, fun a ha => ?_⟩
  have h1 : ∫ u, a u ∂ν = ∫ z, a (π z) * (g z : ℂ) ∂μ := by
    rw [hν, integral_map hπm.aemeasurable ha.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hgm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [NNReal.smul_def, Complex.real_smul, mul_comm]
  rw [← h1, hc, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]
end PositivityTheory.Rg.Sw.Glob.LocCellT
