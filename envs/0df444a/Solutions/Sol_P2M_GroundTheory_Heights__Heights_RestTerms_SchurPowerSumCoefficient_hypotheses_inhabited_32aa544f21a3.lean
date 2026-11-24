-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_hypotheses_inhabited_32aa544f21a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:47.117801+00:00
-- url     : https://prove2.me/submissions/b6b5a90e-9516-486e-b747-2f3a2f40b748

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchurPowerSumCoefficient
theorem _root_.solution :
    1 ≤ 3 ∧ 3 ≤ 3 ∧ Antitone (![2, 1] : Fin 2 → ℕ) ∧ ∑ i, (![2, 1] : Fin 2 → ℕ) i = 3 := by
  refine ⟨by norm_num, le_rfl, ?_, by simp⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
end SchurPowerSumCoefficient
end GroundTheory.Heights₂.Heights.RestTerms
