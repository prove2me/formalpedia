-- Prove2me | solution 1 for P2M_GlobalTheory_T_norm_le_of_recurrence_growth__d6c02f29f6fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:53:08.742654+00:00
-- url     : https://prove2.me/submissions/0463794a-e106-4003-a1b9-eef36c2d7e9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormLeOfRecurrenceGrowth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormLeOfRecurrenceGrowthStatement
import Theorems.Thm_GlobalTheory_norm_le_of_recurrence_growth


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
theorem _root_.solution : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  first | exact @GlobalTheory.norm_le_of_recurrence_growth | exact GlobalTheory.norm_le_of_recurrence_growth | (intros; apply GlobalTheory.norm_le_of_recurrence_growth <;> assumption)
end _root_.GlobalTheory.T
