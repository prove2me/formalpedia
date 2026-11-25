-- Prove2me | solution 1 for PI.Residue.pow_le_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:56.877615+00:00
-- url     : https://prove2.me/submissions/2cd3784f-c15e-4174-8314-6f9a56254066

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_ThirdLeLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (m : ℕ) (hm : 2 ≤ m) :
    (3 / 2 : ℝ) ^ m ≤ 4 / 9 * (3 * Real.pi / 4) ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hpi := Real.pi_gt_three
  have h1 : (3 / 2 : ℝ) ^ k ≤ (3 * Real.pi / 4) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith) k
  have h2 : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ k := by positivity
  have h4 : (0 : ℝ) ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by positivity
  calc (3 / 2 : ℝ) ^ (2 + k) = (3 / 2 : ℝ) ^ 2 * (3 / 2 : ℝ) ^ k := pow_add _ _ _
    _ ≤ (4 / 9 * (3 * Real.pi / 4) ^ 2) * (3 * Real.pi / 4) ^ k := mul_le_mul h2 h1 h3 h4
    _ = 4 / 9 * (3 * Real.pi / 4) ^ (2 + k) := by rw [pow_add]; ring
end PI.Residue
