-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.sum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:13.335303+00:00
-- url     : https://prove2.me/submissions/74ee15a0-2bbe-46dd-92fb-e197f8202388

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution (x : ι → ℝ) : ∑ i, x i ^ 2 ≤ (Fintype.card ι) * ‖x‖ ^ 2 := by
  calc ∑ i, x i ^ 2 ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (Fintype.card ι) * ‖x‖ ^ 2 := by simp
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
