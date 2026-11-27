-- Prove2me | solution 1 for P2M_GlobalTheory_T_summable_rpow_of_fibre_card_le__c55443d5c67b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:38.319813+00:00
-- url     : https://prove2.me/submissions/85bb4a47-f8f3-431d-b841-929e3002fb4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLeStatement
import Theorems.Thm_GlobalTheory_SummCount_summable_rpow_of_fibre_card_le


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
theorem _root_.solution : ∀ (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ) (h : ι → ℝ), 1 < b → (n : ℝ) < t → (∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹) → (∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) → (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) → Summable fun q => h q ^ t := by
  first | exact @GlobalTheory.SummCount.summable_rpow_of_fibre_card_le | exact GlobalTheory.SummCount.summable_rpow_of_fibre_card_le | (intros; apply GlobalTheory.SummCount.summable_rpow_of_fibre_card_le <;> assumption)
end _root_.GlobalTheory.T
