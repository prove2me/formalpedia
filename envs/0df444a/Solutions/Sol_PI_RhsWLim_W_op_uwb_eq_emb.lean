-- Prove2me | solution 1 for PI.RhsWLim.W.op_uwb_eq_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:58.675128+00:00
-- url     : https://prove2.me/submissions/e8ab5f8e-059b-40f6-9501-edbc203112c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_op_uwb_col
import Theorems.Thm_PI_RhsWLim_W_op_uwb_row
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mid
import Theorems.Thm_PI_RhsWLim_W_MB_emb_out_col
import Theorems.Thm_PI_RhsWLim_W_MB_emb_out_row
import Theorems.Thm_PI_RhsWLim_W_MB_wI_midx


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
theorem _root_.solution {g : Mat k r} (hg : g ∈ UWb k r) : g = embWb k r (g.submatrix (wI k r) (wI k r)) := by
  ext i j
  by_cases hj : mid k r j
  · by_cases hi : mid k r i
    · rw [emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]
    · rw [emb_out_row _ i j hi, op_uwb_row hg i j hi]
  · rw [emb_out_col _ i j hj, op_uwb_col hg j i hj]
end PI.RhsWLim.W
