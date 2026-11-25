-- Prove2me | solution 1 for PI.FJMX.shape_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:15.70029+00:00
-- url     : https://prove2.me/submissions/a0bd5262-9e6b-4617-a607-77659bbc2217

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Theorems.Thm_PI_FJMX_tele
import Theorems.Thm_PI_FJMX_getD_succ_le
import Theorems.Thm_PI_FJMX_getD_length

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
theorem _root_.solution (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (i₀ : ℕ) :
    ∑ t ∈ Finset.range α.length, (α.getD t 0 - α.getD (t + 1) 0) • (if i₀ < t + 1 then 1 else 0) =
      α.getD i₀ 0 := by
  have e : ∀ t, (α.getD t 0 - α.getD (t + 1) 0) • (if i₀ < t + 1 then 1 else 0) =
      if i₀ ≤ t then (α.getD t 0 - α.getD (t + 1) 0) else 0 := by
    intro t
    by_cases h : i₀ ≤ t
    · rw [if_pos (by omega), if_pos h]; simp
    · rw [if_neg (by omega), if_neg h]; simp
  simp only [e]
  rw [tele (fun t => α.getD t 0) (getD_succ_le α hα), getD_length]
  split_ifs with h
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp
end PI.FJMX
