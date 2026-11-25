-- Prove2me | solution 1 for PI.Mk.nextCoeff_X_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:58.84302+00:00
-- url     : https://prove2.me/submissions/75898392-a02a-491c-8cb1-3f8e52dae4df

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (X ^ n - 1 : ℚ[X]).nextCoeff = if n = 1 then -1 else 0 := by
  have hdeg : (X ^ n - 1 : ℚ[X]).natDegree = n := by
    simpa using natDegree_X_pow_sub_C (R := ℚ) (n := n) (r := 1)
  rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hn), hdeg]
  split_ifs with h1
  · subst h1; simp
  · have h2 : n - 1 ≠ n := by omega
    have h3 : n - 1 ≠ 0 := by omega
    simp [coeff_X_pow, coeff_one, h2, h3]
end PI.Mk
