-- Prove2me | solution 1 for PI.RhsWLim.W.qf_blkAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:59.46914+00:00
-- url     : https://prove2.me/submissions/c35489b7-13aa-4fd0-bfec-7d35f932b9af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_toW_ofW
import Theorems.Thm_PI_RhsWLim_W_qf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) (p : (Fin k → ℂ) × ℂ) :
    qf k (blkAct k μ p) = qf k p := by
  have h : (qf k (blkAct k μ p) : ℂ) = (qf k p : ℂ) := by
    rw [qf_eq, qf_eq]
    unfold blkAct
    rw [toW_ofW, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]
  exact_mod_cast h
end PI.RhsWLim.W
