-- Prove2me | solution 1 for ThreeSum.TernaryPairedInitialBudget.target_count_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:48.776277+00:00
-- url     : https://prove2.me/submissions/45813662-bc83-43fb-ba6d-90627a599166

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
import Theorems.Thm_ThreeSum_TernaryPairedInitialBudget_fourth_bound
import Theorems.Thm_ThreeSum_TernaryPairedInitialBudget_target_count_le

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitialBudget
namespace ThreeSum.TernaryPairedInitialBudget
theorem _root_.solution (K Λ b n carries targets C : ℕ)
    (ht : targets≤n*carries) (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (targets*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2)^4≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) :=
  (Nat.pow_le_pow_left (target_count_le K Λ b n carries targets ht) 4).trans
    (fourth_bound K Λ b n carries C hcarry)
end ThreeSum.TernaryPairedInitialBudget
