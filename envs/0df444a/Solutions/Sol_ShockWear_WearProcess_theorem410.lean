-- Prove2me | solution 1 for ShockWear.WearProcess.theorem410
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:04:32.522244+00:00
-- url     : https://prove2.me/submissions/ba4ded92-3881-4234-93c7-6823176750f6

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model
import Theorems.Thm_ShockWear_WearProcess_proof410_all_times
import Theorems.Thm_ShockWear_WearProcess_proof410_passSurv_limit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ShockWear.WearProcess

theorem solution {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ) (hZ : IsWearProcess pr Z κ) (x : ℝ) :
    IsIHRA (passSurv pr Z x) := by
  have hexp : ∀ r : ℝ≥0, 0 < (r : ℝ) →
      Tendsto (fun ε : ℝ≥0 => 1 / (((r + ε : ℝ≥0)) : ℝ)) (𝓝[>] 0) (𝓝 (1 / (r : ℝ))) := by
    intro r hr
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun ε : ℝ≥0 => (((r + ε : ℝ≥0)) : ℝ)) := by fun_prop
    have h1 := hc.tendsto 0
    simp only [add_zero] at h1
    simpa only [one_div] using h1.inv₀ hr.ne'
  intro s hs t ht hst
  simp only [Set.mem_Ioi] at hs ht
  simp only
  set s' : ℝ≥0 := s.toNNReal
  set t' : ℝ≥0 := t.toNNReal
  have hs' : (s' : ℝ) = s := Real.coe_toNNReal _ hs.le
  have ht' : (t' : ℝ) = t := Real.coe_toNNReal _ ht.le
  have hlimS := proof410_passSurv_limit pr Z hZ.toIsMonotoneWear x s'
  have hlimT := proof410_passSurv_limit pr Z hZ.toIsMonotoneWear x t'
  have heS := hexp s' (by rw [hs']; exact hs)
  have heT := hexp t' (by rw [ht']; exact ht)
  rw [hs'] at hlimS heS
  rw [ht'] at hlimT heT
  have hS := hlimS.rpow heS (Or.inr (by positivity))
  have hT := hlimT.rpow heT (Or.inr (by positivity))
  apply le_of_tendsto_of_tendsto hT hS
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply proof410_all_times pr Z κ hZ x (s' + ε) (t' + ε)
  · exact add_pos_of_pos_of_nonneg (by rw [← NNReal.coe_pos, hs']; exact hs) (by positivity)
  · gcongr
    rw [← NNReal.coe_le_coe, hs', ht']; exact hst
