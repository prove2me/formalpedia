-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:32.97392+00:00
-- url     : https://prove2.me/submissions/862ba17e-2122-4e56-ac3c-91c70541a9a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}
omit h
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution {z0 z : Fin n → ℂ} {k : Fin n} (hk : k.val < a) (h0 : z0 k ≠ 0)
    (hz : z k ≠ 0) : Complex.exp (branchLift a z0 z k) = z k := by
  simp only [branchLift, if_pos hk]
  rw [Complex.exp_add, Complex.exp_log (div_ne_zero hz h0), Complex.exp_log h0,
    div_mul_cancel₀ _ h0]
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
