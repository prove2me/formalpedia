-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteAtRootsOfUnity_proof_ea526ef96028
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:40.533891+00:00
-- url     : https://prove2.me/submissions/2cc35b41-6d70-42d9-a03f-f9c9a54371df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchCompleteAtRootsOfUnity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_prod_one_sub_rootOfUnityPoint_80e9c307bf5e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchCompleteAtRootsOfUnity
theorem _root_.solution (h1 : SchProdOneSubRootsOfUnity.Statement)
    (h2 : SchCompleteGenerating.Statement) : SchCompleteAtRootsOfUnity.Statement := by
  intro N k d hk hkN
  let H : ℕ → ℂ := fun n => aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ n)
  have hrec : ∀ n, H n - (if k ≤ n then H (n - k) else 0) = if n = 0 then 1 else 0 := by
    intro n
    have e := h2 N (rootOfUnityPoint N k) n
    rw [prod_one_sub_rootOfUnityPoint h1 hk hkN] at e
    rw [← e]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow, sub_mul,
      sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [H]
  show H d = _
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e := hrec d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [if_neg (by omega), sub_zero, if_pos rfl] at e
      rw [e, if_pos (dvd_zero k)]
    · by_cases hkd : k ≤ d
      · rw [if_pos hkd, if_neg (show d ≠ 0 by omega), sub_eq_zero, ih (d - k) (by omega)] at e
        have hdvd : k ∣ d - k ↔ k ∣ d := by
          conv_rhs => rw [show d = d - k + k by omega]
          exact (Nat.dvd_add_self_right).symm
        rw [e]
        exact if_congr hdvd rfl rfl
      · rw [if_neg hkd, if_neg (show d ≠ 0 by omega), sub_zero] at e
        rw [e, if_neg]
        exact fun h => hkd (Nat.le_of_dvd hd h)
end SchCompleteAtRootsOfUnity
end GroundTheory.Heights₂.Heights.RestTerms
