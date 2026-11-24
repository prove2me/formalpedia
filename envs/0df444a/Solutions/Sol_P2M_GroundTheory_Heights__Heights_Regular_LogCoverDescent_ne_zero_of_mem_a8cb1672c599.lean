-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:33.220744+00:00
-- url     : https://prove2.me/submissions/1b074df7-ba37-4a81-9ec9-17db8b93a4c3

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
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n)
    (hk : k.val < a) : z k ≠ 0 := by
  have := hz.2 ⟨k.val, hk⟩
  unfold cuspCoord at this
  rwa [show Fin.castLE h ⟨k.val, hk⟩ = k from Fin.ext rfl] at this
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
