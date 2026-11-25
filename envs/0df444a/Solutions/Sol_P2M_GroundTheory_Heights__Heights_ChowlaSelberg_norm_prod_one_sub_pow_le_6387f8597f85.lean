-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_prod_one_sub_pow_le_6387f8597f85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:44.856107+00:00
-- url     : https://prove2.me/submissions/648669a8-5c98-4d25-ac62-73d93cdaa0c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {x : ℂ} (hx : ‖x‖ < 1) (k n : ℕ) :
    ‖∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ Real.exp (1 - ‖x‖)⁻¹ := by
  rw [norm_prod]
  calc ∏ i ∈ range (n + 1), ‖1 - x ^ (k + i + 1)‖
      ≤ ∏ i ∈ range (n + 1), Real.exp (‖x‖ ^ i) := by
        refine prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
        calc ‖1 - x ^ (k + i + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ (k + i + 1)‖ := norm_sub_le _ _
          _ = ‖x‖ ^ (k + i + 1) + 1 := by rw [norm_one, norm_pow, add_comm]
          _ ≤ ‖x‖ ^ i + 1 := by
            linarith [pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega : i ≤ k + i + 1)]
          _ ≤ Real.exp (‖x‖ ^ i) := Real.add_one_le_exp _
    _ = Real.exp (∑ i ∈ range (n + 1), ‖x‖ ^ i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 - ‖x‖)⁻¹ := by
        gcongr
        rw [← tsum_geometric_of_lt_one (norm_nonneg _) hx]
        exact (summable_geometric_of_lt_one (norm_nonneg _) hx).sum_le_tsum _
          (fun _ _ ↦ by positivity)
end GroundTheory.Heights₂.Heights.ChowlaSelberg
