-- Prove2me | solution 1 for ResolutionCoverBallMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:00.889801+00:00
-- url     : https://prove2.me/submissions/3d74379a-43ef-4a7b-9b70-67e9c213f9fd

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_ResolutionCoverBallMeasure
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_GeodesicMorreyLeTwo


set_option autoImplicit false
open MeasureTheory Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (s : ℕ → ℝ) (hres : IsGeodesicResolution γ k s)
    (J : Finset ℕ) (hJ : J ⊆ Finset.Icc 1 k) (x : E) (r : ℝ) (hr : 0 < r)
    (hcov : {u ∈ Set.Icc (0:ℝ) γ.len | γ.toFun u ∈ Metric.closedBall x r} ⊆
      ⋃ j ∈ J, Set.Icc (s (j - 1)) (s j)) :
    curveMeasure γ (Metric.closedBall x r) ≤ ENNReal.ofReal (2 * (J.card : ℝ) * r) := by
-- BODY
  have hmeas : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
  obtain ⟨hmono, h0, hk, hgeo⟩ := hres
  have hm : ∀ p q : ℕ, p ≤ q → q ≤ k → s p ≤ s q := by
    intro p q hpq hq
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hpq.trans hq⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq
  -- rewrite the ball's `μ_γ`-measure as a Lebesgue measure on the parameter interval
  have heq : curveMeasure γ (Metric.closedBall x r) =
      volume {u ∈ Set.Icc (0:ℝ) γ.len | γ.toFun u ∈ Metric.closedBall x r} := by
    rw [curveMeasure, Measure.map_apply hmeas measurableSet_closedBall,
      Measure.restrict_apply (hmeas measurableSet_closedBall)]
    congr 1
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    tauto
  rw [heq]
  -- refine the covering so that each piece also lies in the ball's preimage
  have hcov' : {u ∈ Set.Icc (0:ℝ) γ.len | γ.toFun u ∈ Metric.closedBall x r} ⊆
      ⋃ j ∈ J, (γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (s (j - 1)) (s j) := by
    intro u hu
    have hu' := hcov hu
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, exists_prop] at hu' ⊢
    obtain ⟨j, hj, hju⟩ := hu'
    exact ⟨j, hj, hu.2, hju⟩
  -- each edge contributes at most `2r`
  have hterm : ∀ j ∈ J,
      volume ((γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (s (j - 1)) (s j)) ≤
        ENNReal.ofReal (2 * r) := by
    intro j hj
    have hjr := Finset.mem_Icc.mp (hJ hj)
    obtain ⟨hj1, hjk⟩ := hjr
    have hsucc : j - 1 + 1 = j := by omega
    have hgj : IsGeodesicOn γ (s (j - 1)) (s (j - 1 + 1)) := hgeo (j - 1) (by omega)
    rw [hsucc] at hgj
    have hab : s (j - 1) ≤ s j := hm (j - 1) j (by omega) hjk
    have hbnd : s j ≤ γ.len := by
      have := hm j k hjk le_rfl; rw [hk] at this; exact this
    have hmorrey := GeodesicMorreyLeTwo γ (s (j - 1)) (s j) hab hbnd hgj
    have hpt : Measure.map γ.toFun (volume.restrict (Set.Icc (s (j - 1)) (s j)))
        (Metric.closedBall x r) / ENNReal.ofReal r ≤ 2 := by
      refine le_trans ?_ hmorrey
      simp only [morreyNorm]
      exact le_iSup_of_le x (le_iSup_of_le r (le_iSup_of_le hr le_rfl))
    rw [ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top] at hpt
    rw [Measure.map_apply hmeas measurableSet_closedBall,
      Measure.restrict_apply (hmeas measurableSet_closedBall)] at hpt
    refine hpt.trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  calc volume {u ∈ Set.Icc (0:ℝ) γ.len | γ.toFun u ∈ Metric.closedBall x r}
      ≤ volume (⋃ j ∈ J, (γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (s (j - 1)) (s j)) :=
        measure_mono hcov'
    _ ≤ ∑ j ∈ J, volume ((γ.toFun ⁻¹' Metric.closedBall x r) ∩ Set.Icc (s (j - 1)) (s j)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ J, ENNReal.ofReal (2 * r) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * (J.card : ℝ) * r) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast J.card,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
