-- Prove2me | solution 1 for StochasticOrders.MultivariateVariability.icx_submartingale_coupling_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:08:06.026369+00:00
-- url     : https://prove2.me/submissions/63dc39cd-2f4a-4ec4-9f74-f65a12103e14

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_IcxOrder
import Theorems.Thm_PalmQueueing_Ordering_strassen_cx
open MeasureTheory ProbabilityTheory
namespace CPL97MICX

theorem convex_continuous {n : ℕ} {φ : (Fin n → ℝ) → ℝ} (h : ConvexOn ℝ Set.univ φ) :
    Continuous φ :=
  continuousOn_univ.mp (h.continuousOn isOpen_univ)

theorem icx_iff {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) :
    StochasticOrders.MultivariateVariability.IcxOrder μ ν X Y ↔
      PalmQueueing.Ordering.IcxLe (μ.map X) (ν.map Y) := by
  constructor
  · intro h φ hφ hFi hGi
    have hc := convex_continuous hφ.2
    have hmono : Monotone φ := fun x y hxy => hφ.1 x y hxy
    rw [integrable_map_measure hc.aestronglyMeasurable hX.aemeasurable] at hFi
    rw [integrable_map_measure hc.aestronglyMeasurable hY.aemeasurable] at hGi
    rw [integral_map hX.aemeasurable hc.aestronglyMeasurable,
      integral_map hY.aemeasurable hc.aestronglyMeasurable]
    exact h φ hmono hφ.2 hFi hGi
  · intro h φ hmono hconv hFi hGi
    have hc := convex_continuous hconv
    have := h φ ⟨fun x y hxy => hmono hxy, hconv⟩
      ((integrable_map_measure hc.aestronglyMeasurable hX.aemeasurable).mpr hFi)
      ((integrable_map_measure hc.aestronglyMeasurable hY.aemeasurable).mpr hGi)
    rwa [integral_map hX.aemeasurable hc.aestronglyMeasurable,
      integral_map hY.aemeasurable hc.aestronglyMeasurable] at this

end CPL97MICX

open StochasticOrders.MultivariateVariability in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] := by
  have hF : PalmQueueing.Ordering.IsDistribution (μ.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hG : PalmQueueing.Ordering.IsDistribution (ν.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hFi : PalmQueueing.Ordering.IsIntegrableDist (μ.map X) :=
    (integrable_map_measure continuous_norm.aestronglyMeasurable hX.aemeasurable).mpr hXint.norm
  have hGi : PalmQueueing.Ordering.IsIntegrableDist (ν.map Y) :=
    (integrable_map_measure continuous_norm.aestronglyMeasurable hY.aemeasurable).mpr hYint.norm
  rw [CPL97MICX.icx_iff μ ν X Y hX hY,
    (PalmQueueing.Ordering.strassen_cx _ _ hF hG hFi hGi).2]
  constructor
  · rintro ⟨Ω'', m, P, hP, Xh, Yh, hXh, hYh, hmX, hmY, hle⟩
    exact ⟨Ω'', m, P, hP, Xh, Yh, hXh, hYh, ⟨hXh.aemeasurable, hX.aemeasurable, hmX⟩,
      ⟨hYh.aemeasurable, hY.aemeasurable, hmY⟩, hle.mono fun ω h => h⟩
  · rintro ⟨Ω'', m, P, hP, Xh, Yh, hXh, hYh, hiX, hiY, hle⟩
    exact ⟨Ω'', m, P, hP, Xh, Yh, hXh, hYh, hiX.map_eq, hiY.map_eq, hle.mono fun ω h => h⟩
