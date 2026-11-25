-- Prove2me | solution 1 for PI.RhsWLim.W.RI.herm_e_wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:41.941946+00:00
-- url     : https://prove2.me/submissions/cbb1febc-8310-4550-b2f9-d26fb0318600

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF

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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : herm (Hpk k r) (bvec j) d = 0 := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  refine Finset.sum_eq_zero fun i _ => ?_
  show star (d i) * Hpk k r i j = 0
  rw [HU.hpk_row]
  split_ifs with h
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hd i hi, star_zero, zero_mul]
    · exfalso
      rw [Fin.ext_iff] at h
      unfold HU.tau at h
      simp only [hi, if_false] at h
      omega
  · exact mul_zero _
end PI.RhsWLim.W.RI
