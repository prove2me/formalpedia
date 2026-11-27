-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.aap_lintegral_chart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:19.156559+00:00
-- url     : https://prove2.me/submissions/c45edf9c-38c8-46ac-bab8-ef5bce71c251

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (i : ι) (f : Y → ℝ≥0∞) (hf : Measurable f) (s : Set (V n))
    (hs : s ⊆ (A.chart i).target) :
    ∫⁻ v in s, f ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ ∫⁻ y, f y ∂A.mu := by
  set φ := A.chart i
  set dens : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i (φ.symm v)))
  set ν := (volume.restrict φ.target).withDensity dens
  have hsymm0 : AEMeasurable φ.symm (volume.restrict φ.target) :=
    φ.continuousOn_symm.aemeasurable φ.open_target.measurableSet
  have hsymm : AEMeasurable φ.symm ν := hsymm0.mono_ac (withDensity_absolutelyContinuous _ _)
  have hdens : AEMeasurable dens (volume.restrict φ.target) := by
    have hc : ContinuousOn dens φ.target :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)
    exact hc.aemeasurable φ.open_target.measurableSet
  have hmeas : A.mu.restrict φ.source = ν.map φ.symm := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.map_apply_of_aemeasurable hsymm hB, withDensity_apply',
      Measure.restrict_restrict' φ.open_target.measurableSet,
      A.mu_chart i _ (hB.inter φ.open_source.measurableSet) Set.inter_subset_right]
    have hset : φ '' (B ∩ φ.source) = φ.symm ⁻¹' B ∩ φ.target := by
      rw [Set.inter_comm, φ.image_source_inter_eq', Set.inter_comm]
    rw [hset]
  calc ∫⁻ v in s, f (φ.symm v) * dens v
      ≤ ∫⁻ v in φ.target, f (φ.symm v) * dens v := lintegral_mono_set hs
    _ = ∫⁻ v in φ.target, dens v * f (φ.symm v) := by simp_rw [mul_comm]
    _ = ∫⁻ v, f (φ.symm v) ∂ν := (lintegral_withDensity_eq_lintegral_mul₀ hdens
          (hf.comp_aemeasurable hsymm0)).symm
    _ = ∫⁻ y, f y ∂(ν.map φ.symm) := (lintegral_map' hf.aemeasurable hsymm).symm
    _ = ∫⁻ y in φ.source, f y ∂A.mu := by rw [hmeas]
    _ ≤ ∫⁻ y, f y ∂A.mu := setLIntegral_le_lintegral _ _
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
