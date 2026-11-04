-- Prove2me | solution 1 for ThreeSum.TernaryPairedRecurrence.paired_fourth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:03.389003+00:00
-- url     : https://prove2.me/submissions/afbfa108-6e9a-49ef-8a51-1126bf7522f9

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Theorems.Thm_ThreeSum_TernaryPairedRecurrence_weighted_iteration

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence
namespace ThreeSum.TernaryPairedRecurrence
theorem _root_.solution (K M a b : ℕ) (ha : 0<a) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1)≤b*score j)
    (hbudget : b^4*M^(4*K+3)≤a^4) (r : ℕ) :
    M^(r*(4*K+3))*(score r)^4≤(score 0)^4 := by
  have hs (j : ℕ) : a^4*(score (j+1))^4≤b^4*(score j)^4 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left (hstep j) 4
  have hh := weighted_iteration (a^4) (b^4) (M^(4*K+3)) (pow_pos ha 4)
    (fun j => (score j)^4) hs hbudget r
  simpa only [←pow_mul,mul_comm (4*K+3) r] using hh
end ThreeSum.TernaryPairedRecurrence
