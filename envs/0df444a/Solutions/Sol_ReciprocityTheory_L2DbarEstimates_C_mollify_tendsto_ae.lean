-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mollify_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:33.857595+00:00
-- url     : https://prove2.me/submissions/a5dac7b5-1c0b-4cbb-b47e-db947ab5fcde

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollLeClosedBall
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_le_closedBall
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_integral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_tsupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {u : V n → ℂ} (hu : Integrable u) :
    ∀ᵐ x, Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (u x)) := by
  obtain ⟨C, hC⟩ := moll_le_closedBall n
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume)
    hu.locallyIntegrable 1] with x hx
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hav : Tendsto (fun t : ℝ => ⨍ y in closedBall x t, ‖u y - u x‖) (𝓝[>] 0) (𝓝 0) :=
    hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id (by
      filter_upwards [hpos] with t ht
      exact mem_closedBall_self (by simp only [id, one_mul]; exact ht.le))
  have hg : Tendsto (fun t : ℝ => ∫ y, moll n t (x - y)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with t ht
    show (1 : ℝ) = ∫ y, moll n t (x - y)
    rw [integral_sub_left_eq_self (moll n t) volume x, moll_integral n ht]
  have hsupp : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Function.support (fun y => moll n t (x - y)) ⊆ closedBall x t := by
    filter_upwards [hpos] with t ht
    intro y hy
    have h := moll_tsupport n ht (subset_tsupport (moll n t) (show x - y ∈ Function.support (moll n t) from hy))
    rw [mem_closedBall, dist_zero_right] at h
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    linarith
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y, |moll n t (x - y)| ≤ C / volume.real (closedBall x t) := by
    filter_upwards [hpos] with t ht
    intro y
    rw [abs_of_nonneg (moll_nonneg _ _ _)]
    exact hC t ht x _
  have key := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
    (a := fun t => closedBall x t) (g := fun t y => moll n t (x - y)) C hav
    (Eventually.of_forall fun _ => hu.integrableOn) hg hsupp hbd
  refine key.congr (fun t => ?_)
  simp only [mollify, Complex.real_smul]
end ReciprocityTheory.L2DbarEstimates.C
