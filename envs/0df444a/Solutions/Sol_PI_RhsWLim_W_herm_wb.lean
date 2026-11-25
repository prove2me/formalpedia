-- Prove2me | solution 1 for PI.RhsWLim.W.herm_wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:20.829649+00:00
-- url     : https://prove2.me/submissions/69c50dcb-774d-4d24-aa7a-21ec41cd5348

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Theorems.Thm_PI_RhsWLim_W_sum_wb
import Theorems.Thm_PI_RhsWLim_W_tau_wI
import Theorems.Thm_PI_RhsWLim_W_hpk_mulVec_apply
import Theorems.Thm_PI_RhsWLim_W_sgn_wI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (v z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) v z = herm (Hb k) (wbPart k r v) (wbPart k r z) := by
  simp only [PI.RhsWLim.herm, dotProduct]
  rw [sum_wb (k := k) (r := r)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.star_apply, hpk_mulVec_apply, PI.RhsWLim.Hb, Matrix.mulVec_diagonal, PI.RhsWLim.wbPart,
      sgn_wI, tau_wI]
  · intro i hi
    simp [hz i hi]
end PI.RhsWLim.W
