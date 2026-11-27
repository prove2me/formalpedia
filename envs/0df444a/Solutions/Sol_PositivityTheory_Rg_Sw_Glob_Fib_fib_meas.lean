-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.Fib.fib_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:51.077098+00:00
-- url     : https://prove2.me/submissions/3a9790d4-d56a-4ec3-abf1-6b047cff6669

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_FibFact

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.Fib
variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X]
  [BorelSpace X]
namespace PositivityTheory.Rg.Sw.Glob.Fib
theorem _root_.solution (μ : Measure X) [μ.IsAddRightInvariant] (π : X →+ (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) →+ X) (hπs : ∀ u, π (s u) = u) (g : X → ℝ≥0∞) (hg : Measurable g)
    (hgs : ∀ z u, g (z + s u) = g z)
    (hloc : ∀ K : Set (Fin m → Fin n → ℂ), IsCompact K → ∫⁻ z, K.indicator 1 (π z) * g z ∂μ ≠ ∞) :
    ∃ c : ℝ≥0, (μ.withDensity g).map π = c • (volume : Measure (Fin m → Fin n → ℂ)) := by
  set ν : Measure (Fin m → Fin n → ℂ) := (μ.withDensity g).map π with hν
  have hπm : Measurable π := hπ.measurable
  have hint : ∀ a : (Fin m → Fin n → ℂ) → ℝ≥0∞, Measurable a → ∫⁻ u, a u ∂ν = ∫⁻ z, a (π z) * g z ∂μ := by
    intro a ha
    rw [hν, lintegral_map ha hπm]
    have e := lintegral_withDensity_eq_lintegral_mul μ hg (ha.comp hπm)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  have hinv : ν.IsAddLeftInvariant := by
    refine ⟨fun u => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_add u) hA, ← lintegral_indicator_one (measurable_const_add u hA),
      ← lintegral_indicator_one hA, hint _ (measurable_one.indicator (measurable_const_add u hA)),
      hint _ (measurable_one.indicator hA)]
    have key : ∀ z, ((fun x => u + x) ⁻¹' A).indicator 1 (π z) * g z =
        (fun z => A.indicator 1 (π z) * g z) (z + s u) := by
      intro z
      simp only [map_add, hπs, hgs]
      congr 1
      by_cases h : u + π z ∈ A
      · simp [Set.indicator, h, add_comm]
      · simp [Set.indicator, h, add_comm]
    simp_rw [key]
    exact lintegral_add_right_eq_self (fun z => A.indicator 1 (π z) * g z) (s u)
  have hfc : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [← lintegral_indicator_one hK.measurableSet, hint _ (measurable_one.indicator hK.measurableSet)]
    exact (hloc K hK).lt_top
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact ⟨Measure.addHaarScalarFactor ν volume, Measure.isAddLeftInvariant_eq_smul ν volume⟩
end PositivityTheory.Rg.Sw.Glob.Fib
