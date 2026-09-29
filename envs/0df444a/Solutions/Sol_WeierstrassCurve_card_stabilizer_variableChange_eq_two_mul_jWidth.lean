-- Prove2me | solution 1 for WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c2228c47-d1d5-53a8-a915-34491c681837

import Mathlib
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) W) =
      2 * ModularCurve.jWidth W.j := by
  have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero h2
  have h3' : (3 : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact h3 h1
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2' h2'
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]; exact mul_ne_zero h2' h3'
  have h1728 : (1728 : K) ≠ 0 := by
    rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2') (pow_ne_zero _ h3')
  haveI : NeZero ((4 : ℕ) : K) := ⟨by exact_mod_cast h4⟩
  haveI : NeZero ((6 : ℕ) : K) := ⟨by exact_mod_cast h6⟩
  by_cases hj0 : W.j = 0
  · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
      h2' h3' W hj0, HasEnoughRootsOfUnity.natCard_rootsOfUnity K 6, hj0]
    simp [ModularCurve.jWidth]
  · by_cases hj1728 : W.j = 1728
    · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_four_of_j_eq_1728
        h2' h3' W hj1728, HasEnoughRootsOfUnity.natCard_rootsOfUnity K 4, hj1728]
      simp [ModularCurve.jWidth, h1728]
    · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
        h2' h3' W hj0 hj1728]
      simp [ModularCurve.jWidth, hj0, hj1728]

end S_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth
end P2MW
export P2MW.S_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth (solution)
