-- Prove2me | solution 1 for ThreeSum.TernaryPairedInitialBudget.target_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:09.685193+00:00
-- url     : https://prove2.me/submissions/df354aeb-b5ed-4519-a9e0-cd4f44c9fb75

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitialBudget
namespace ThreeSum.TernaryPairedInitialBudget
theorem _root_.solution (K Λ b n carries targets : ℕ) (ht : targets≤n*carries) :
    targets*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2≤upper K Λ b n carries := by
  unfold upper
  calc
    _ ≤ (n*carries)*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
      gcongr
    _ = _ := by rw [pow_succ]; ring
end ThreeSum.TernaryPairedInitialBudget
