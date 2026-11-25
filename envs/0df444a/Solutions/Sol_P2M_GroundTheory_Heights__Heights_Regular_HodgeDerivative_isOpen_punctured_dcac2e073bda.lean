-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_isOpen_punctured_dcac2e073bda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:58.940065+00:00
-- url     : https://prove2.me/submissions/8b87818b-d732-43ee-ac78-7c593544eb7b

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
theorem _root_.solution {n a : ℕ} (h : a ≤ n) :
    IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have e : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z : Fin n → ℂ | z (Fin.castLE h j) ≠ 0} := by
    ext z
    simp [puncturedChart, cuspCoord]
  rw [e]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
