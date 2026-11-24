-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:32.349472+00:00
-- url     : https://prove2.me/submissions/52ac82b1-9acb-49e4-aff6-b8fbc37e8347

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative

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
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
theorem _root_.solution {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ} (hz : ∀ j, cuspCoord h z j ≠ 0) :
    expCover a (logLift a z) = z := by
  funext k
  by_cases hk : k.val < a
  · have e : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
    have h0 : z k ≠ 0 := by
      have := hz ⟨k.val, hk⟩
      rwa [cuspCoord, e] at this
    simp only [expCover, logLift, if_pos hk, Complex.exp_log h0]
  · simp only [expCover, logLift, if_neg hk]
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
