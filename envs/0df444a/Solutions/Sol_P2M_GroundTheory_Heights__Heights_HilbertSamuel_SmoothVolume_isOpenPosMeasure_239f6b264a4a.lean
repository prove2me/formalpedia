-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmoothVolume_isOpenPosMeasure_239f6b264a4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:39.967425+00:00
-- url     : https://prove2.me/submissions/f3fdc056-fa7a-44b0-bd09-08b23c5ff60a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
variable [MeasurableSpace X] [BorelSpace X]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace SmoothVolume
theorem _root_.solution (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hxU⟩ hzero => ?_⟩
  obtain ⟨j, hx⟩ := A.cover x
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U with hOdef
  have hO : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hU
  have hxO : A.chart j x ∈ O :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hOt : O ⊆ (A.chart j).target := inter_subset_left
  have hmeas : Measurable (U.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have h1 := dV.chart_lintegral j _ hmeas
  have hL : ∫⁻ y in (A.chart j).source, U.indicator (1 : X → ℝ≥0∞) y ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left hzero
  rw [hL] at h1
  have h2 : ∫⁻ y in O, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in O, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in O, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := by
          refine setLIntegral_congr_fun hO.measurableSet fun y hy => ?_
          rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hOt
      _ = 0 := h1.symm
  have hae : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y)) (volume.restrict O) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((dV.smooth j).continuousOn).mono hOt).aemeasurable hO.measurableSet)
  have h3 := (lintegral_eq_zero_iff' hae).1 h2
  rw [EventuallyEq, ae_restrict_iff' hO.measurableSet] at h3
  have h4 : volume O = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h3] with y hy hyO
    exact (ENNReal.ofReal_pos.2 (dV.pos j y (hOt hyO))).ne' (hy hyO)
  exact hO.measure_ne_zero volume ⟨_, hxO⟩ h4
end SmoothVolume
end GroundTheory.Heights₂.Heights.HilbertSamuel
