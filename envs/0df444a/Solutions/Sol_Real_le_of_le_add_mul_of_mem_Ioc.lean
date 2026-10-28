-- Prove2me | solution 1 for Real.le_of_le_add_mul_of_mem_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:19:05.513343+00:00
-- url     : https://prove2.me/submissions/47bef36d-3933-4c27-a24b-26a66cb449ab

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

-- carved verbatim out of submission e3454a9c-3502-4c6b-9794-7eebefc4332c, lines 81-89

section
open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem solution {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

end
