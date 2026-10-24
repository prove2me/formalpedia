-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P03.pure_mode_endpoint_limits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:02:49.827978+00:00
-- url     : https://prove2.me/submissions/aed94e3e-87de-4cf5-987b-e711b0d4e012

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03

namespace QAlgorithms.Papers.Independent.Support50.P03

open Filter Topology Real

theorem x5pm_arcoth (l : ℝ) (hl : 1 / 2 < l) :
    realArcoth (2 * l) = (Real.log (2 * l - 1 + 2) - Real.log (2 * l - 1)) / 2 := by
  unfold realArcoth
  have h1 : 2 * l - 1 ≠ 0 := by linarith
  have h2 : 2 * l + 1 ≠ 0 := by linarith
  rw [Real.log_div h2 h1]
  ring_nf

theorem x5pm_sq (t : ℝ) (ht : 0 < t) : (Real.log t * t ^ (1 / 2 : ℝ)) ^ 2 = t * Real.log t ^ 2 := by
  rw [← Real.sqrt_eq_rpow, mul_pow, Real.sq_sqrt ht.le]; ring

theorem x5pm_F2 (l : ℝ) (hl : 1 / 2 < l) :
    pureModeF2 l = (2 * l - 1 + 2) / 2 * ((2 * l - 1) * Real.log (2 * l - 1 + 2) -
      (2 * l - 1) * Real.log (2 * l - 1)) := by
  unfold pureModeF2
  rw [if_neg hl.ne', x5pm_arcoth l hl]
  ring

theorem x5pm_F1 (l : ℝ) (hl : 1 / 2 < l) :
    pureModeF1 l = (2 * l - 1 + 2) / 4 * ((2 * l - 1) * Real.log (2 * l - 1 + 2) ^ 2 -
      2 * Real.log (2 * l - 1 + 2) * ((2 * l - 1) * Real.log (2 * l - 1)) +
      (Real.log (2 * l - 1) * (2 * l - 1) ^ (1 / 2 : ℝ)) ^ 2) := by
  unfold pureModeF1
  rw [if_neg hl.ne', x5pm_arcoth l hl, x5pm_sq _ (by linarith)]
  ring

theorem x5pm_lim :
    Tendsto pureModeF1 (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) ∧
    Tendsto pureModeF2 (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  have hT : Tendsto (fun l : ℝ => 2 * l - 1) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun l : ℝ => 2 * l - 1) (𝓝 (1 / 2 : ℝ)) (𝓝 (2 * (1 / 2) - 1)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto _
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with l hl
      simp only [Set.mem_Ioi] at hl ⊢; linarith
  have hA : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hB : Tendsto (fun t : ℝ => Real.log t * t ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have hC : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hD : Tendsto (fun t : ℝ => Real.log (t + 2)) (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have hc : ContinuousAt (fun t : ℝ => Real.log (t + 2)) 0 :=
      show ContinuousAt (Real.log ∘ fun t : ℝ => t + 2) 0 from
        ContinuousAt.comp (x := (0 : ℝ)) (Real.continuousAt_log (by norm_num))
          (continuous_add_const (2 : ℝ)).continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hE : Tendsto (fun t : ℝ => t + 2) (𝓝[>] 0) (𝓝 2) := by
    simpa using hC.add_const (2 : ℝ)
  have g2 : Tendsto (fun t : ℝ => (t + 2) / 2 * (t * Real.log (t + 2) - t * Real.log t))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hE.div_const 2).mul ((hC.mul hD).sub hA)
    simpa using this
  have g1 : Tendsto (fun t : ℝ => (t + 2) / 4 * (t * Real.log (t + 2) ^ 2 -
      2 * Real.log (t + 2) * (t * Real.log t) + (Real.log t * t ^ (1 / 2 : ℝ)) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hE.div_const 4).mul (((hC.mul (hD.pow 2)).sub
      ((hD.const_mul 2).mul hA)).add (hB.pow 2))
    simpa using this
  constructor
  · refine (g1.comp hT).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact (x5pm_F1 l hl).symm
  · refine (g2.comp hT).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact (x5pm_F2 l hl).symm

end QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Support50.P03 Filter in
theorem solution :
    Tendsto pureModeF1 (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds 0) ∧
    Tendsto pureModeF2 (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds 0) ∧
    pureModeF1 (1 / 2) = 0 ∧ pureModeF2 (1 / 2) = 0 :=
  ⟨x5pm_lim.1, x5pm_lim.2, by simp [pureModeF1], by simp [pureModeF2]⟩
