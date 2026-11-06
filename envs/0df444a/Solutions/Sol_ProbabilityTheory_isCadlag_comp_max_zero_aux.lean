-- Prove2me | solution 1 for ProbabilityTheory.isCadlag_comp_max_zero_aux
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:18:42.484206+00:00
-- url     : https://prove2.me/submissions/2e97af4e-a550-4909-92f0-6ebb1c90f756

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_IsCadlagAt_congr
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

theorem solution {f : ℝ → ℝ} (hf : IsCadlag f) (h0 : f 0 = 0) :
    IsCadlag (fun t : ℝ => f (max t 0)) := by
  have hcadconst : IsCadlag (fun _ : ℝ => f 0) := by
    intro s
    exact ⟨continuousWithinAt_const, ⟨f 0, tendsto_const_nhds⟩⟩
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · refine (hcadconst t).congr ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [max_eq_right (le_of_lt (Set.mem_Iio.mp hs))]
  · subst ht
    refine ⟨?_, 0, ?_⟩
    · refine ((hf 0).1).congr (fun y hy => ?_) ?_
      · rw [max_eq_left (Set.mem_Ici.mp hy)]
      · rw [max_eq_left (le_refl (0 : ℝ))]
    · have heq : (fun s => f (max s 0)) =ᶠ[𝓝[Set.Iio 0] 0] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [max_eq_right (le_of_lt (Set.mem_Iio.mp hs)), h0]
      exact tendsto_const_nhds.congr' heq.symm
  · refine (hf t).congr ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [max_eq_left (le_of_lt (Set.mem_Ioi.mp hs))]
