-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_norm_iteratedFDeriv_real_inv_797cefa0a45b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:28.866965+00:00
-- url     : https://prove2.me/submissions/8737a3f7-13d3-4880-a0ee-c03642da40e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsInvDerivDecay
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PInvDerivDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Nat Set Filter Topology
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ k (Inv.inv : ℂ → ℂ) z‖ = k ! * (‖z‖ ^ (k + 1))⁻¹ := by
  rw [← (contDiffAt_inv ℂ hz (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
