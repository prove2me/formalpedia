-- Prove2me | solution 1 for Thm_1_4.upper_lower_gap_small_continuous_id
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:15:50.24319+00:00
-- url     : https://prove2.me/submissions/9adb5a1a-51a2-4888-b7bb-dc289e83959c

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Theorems.Thm_Thm_1_4_partition_length_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

private theorem source_upper_lower_gap_small_continuous_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    ClosedIntervalDarbouxGapSmall a b g (fun x => x) := by
  intro eps heps
  let eta : ℝ := eps / (b - a + 1)
  have hspan_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt hab)
  have hden_pos : 0 < b - a + 1 := by linarith
  have heta_pos : 0 < eta := div_pos heps hden_pos
  have hsmall_eta_span : eta * (b - a) < eps := by
    have hspan_lt : b - a < b - a + 1 := by linarith
    have hmul_lt := mul_lt_mul_of_pos_left hspan_lt heta_pos
    have heta_den : eta * (b - a + 1) = eps := by
      dsimp [eta]
      field_simp [ne_of_gt hden_pos]
    linarith
  have hunif : UniformContinuousOn g (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta_pos) with
    ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hAbove : BddAbove (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  have hstep :
      ∀ i : Fin P.n,
        upperStep P g i - lowerStep P g i ≤ eta := by
    intro i
    refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P i hAbove hBelow ?_
    intro x hx y hy
    have hxI : x ∈ Set.Icc a b :=
      DarbouxRS.subinterval_subset_Icc_core P hx
    have hyI : y ∈ Set.Icc a b :=
      DarbouxRS.subinterval_subset_Icc_core P hy
    have hxy_len : |x - y| ≤ P.pts i.succ - P.pts i.castSucc :=
      abs_sub_le_cell_length_of_mem_subinterval P hx hy
    have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh :=
      partition_length_le_mesh_core P i
    have hdist : dist x y < δ := by
      simpa [Real.dist_eq] using
        lt_of_le_of_lt (le_trans hxy_len hlen_mesh) hmesh
    exact le_of_lt (by
      simpa [Real.dist_eq] using Hδ x hxI y hyI hdist)
  have hosc_le :
      partitionOscillation P g (fun x => x) ≤ eta * (b - a) := by
    unfold partitionOscillation
    calc
      (∑ i : Fin P.n,
          (upperStep P g i - lowerStep P g i) *
            ((fun x : ℝ => x) (P.pts i.succ) -
              (fun x : ℝ => x) (P.pts i.castSucc)))
          ≤ ∑ i : Fin P.n,
              eta * (P.pts i.succ - P.pts i.castSucc) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hlen_nonneg : 0 ≤ P.pts i.succ - P.pts i.castSucc :=
              sub_nonneg.mpr (le_of_lt (P.strict_mono Fin.castSucc_lt_succ))
            simpa using mul_le_mul_of_nonneg_right (hstep i) hlen_nonneg
      _ = eta * (b - a) := by
            rw [← Finset.mul_sum, partition_length_sum P]
  calc
    upperSum P g (fun x => x) - lowerSum P g (fun x => x)
        = partitionOscillation P g (fun x => x) :=
          upperSum_sub_lowerSum_eq_partitionOscillation P
    _ ≤ eta * (b - a) := hosc_le
    _ < eps := hsmall_eta_span

theorem solution {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    ClosedIntervalDarbouxGapSmall a b g (fun x => x) := by
  exact source_upper_lower_gap_small_continuous_id hab hg
