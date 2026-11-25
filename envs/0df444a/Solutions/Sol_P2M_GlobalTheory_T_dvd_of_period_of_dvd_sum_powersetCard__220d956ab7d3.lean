-- Prove2me | solution 1 for P2M_GlobalTheory_T_dvd_of_period_of_dvd_sum_powersetCard__220d956ab7d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:55.755266+00:00
-- url     : https://prove2.me/submissions/e186df34-0650-4799-97db-264a9d915f7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCardStatement
import Theorems.Thm_GlobalTheory_dvd_of_period_of_dvd_sum_powersetCard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → (∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i)) → ∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l := by
  first | exact @GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | exact GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | (intros; apply GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard <;> assumption)
end _root_.GlobalTheory.T
