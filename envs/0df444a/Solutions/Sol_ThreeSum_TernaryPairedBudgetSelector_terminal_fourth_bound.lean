-- Prove2me | solution 1 for ThreeSum.TernaryPairedBudgetSelector.terminal_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:07.218196+00:00
-- url     : https://prove2.me/submissions/f4c6863b-ee92-41c3-a0d6-c024fb431eee

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.TernaryPairedBudgetSelector
theorem _root_.solution (K M a b U value r : ℕ) (hb : 0<b)
    (hbudget : a^r*value≤b^r*U) (hdrift : b^4*M^(4*K+3)≤a^4) :
    M^(r*(4*K+3))*value^4≤U^4 := by
  have hp := Nat.pow_le_pow_left hbudget 4
  have hd := Nat.pow_le_pow_left hdrift r
  have hh : (b^4)^r*(M^(r*(4*K+3))*value^4)≤(b^4)^r*U^4 := by
    calc
      _ = (b^4*M^(4*K+3))^r*value^4 := by
        have hm : (M^(4*K+3))^r=M^(r*(4*K+3)) := by rw [←pow_mul,Nat.mul_comm]
        rw [mul_pow,hm]
        ring
      _ ≤ (a^4)^r*value^4 := Nat.mul_le_mul_right _ hd
      _ = (a^r*value)^4 := by
        have he : (a^4)^r=(a^r)^4 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        rw [mul_pow,he]
      _ ≤ (b^r*U)^4 := hp
      _ = _ := by
        have he : (b^r)^4=(b^4)^r := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        rw [mul_pow,he]
  exact Nat.le_of_mul_le_mul_left hh (pow_pos (pow_pos hb 4) r)
end ThreeSum.TernaryPairedBudgetSelector
