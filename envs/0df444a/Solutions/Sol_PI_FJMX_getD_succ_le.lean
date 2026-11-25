-- Prove2me | solution 1 for PI.FJMX.getD_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:27.033477+00:00
-- url     : https://prove2.me/submissions/f91fdac5-68ea-4b6e-b149-a0c29d2e7ebd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (t : ℕ) :
    α.getD (t + 1) 0 ≤ α.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : t + 1 < α.length
  · rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    exact (List.pairwise_iff_getElem.1 hα) t (t + 1) (by omega) h (by omega)
  · rw [List.getElem?_eq_none (by omega)]
    simp
end PI.FJMX
