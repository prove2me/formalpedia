-- Prove2me | solution 1 for PI.Mk.good_cyclotomic_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:42.570645+00:00
-- url     : https://prove2.me/submissions/60b6836c-bf29-4195-a4d9-5796bc198071

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution (ℓ : ℕ) : Good ℓ (cyclotomic 1 ℚ) := by
  rw [cyclotomic_one, ← C_1]
  refine ⟨monic_X_sub_C 1, 0, by simp, ?_, fun _ => ?_⟩
  · rw [natDegree_X_sub_C, nextCoeff_X_sub_C]; simp
  · rw [natDegree_X_sub_C, pow_one, C_1]
end PI.Mk
