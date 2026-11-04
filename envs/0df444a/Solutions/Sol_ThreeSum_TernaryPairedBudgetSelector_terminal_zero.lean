-- Prove2me | solution 1 for ThreeSum.TernaryPairedBudgetSelector.terminal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:06.633259+00:00
-- url     : https://prove2.me/submissions/0827160f-7795-4338-b983-f5786ba02e14

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
import Theorems.Thm_ThreeSum_TernaryPairedBudgetSelector_terminal_fourth_bound

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.TernaryPairedBudgetSelector
theorem _root_.solution (K M a b U value r n C : ℕ) (hb : 0<b)
    (hbudget : a^r*value≤b^r*U) (hdrift : b^4*M^(4*K+3)≤a^4)
    (hcover : n^2≤M^r) (hinit : U^4≤C*n^(8*K+5)) (hn : C<n) : value=0 := by
  have hbound := terminal_fourth_bound K M a b U value r hb hbudget hdrift
  have hbase : n^(8*K+6)≤M^(r*(4*K+3)) := by
    simpa only [←pow_mul,show 2*(4*K+3)=8*K+6 by ring] using Nat.pow_le_pow_left hcover (4*K+3)
  have hnpos : 0<n := by omega
  have hstrict : C*n^(8*K+5)<n^(8*K+6) := by
    have hh := Nat.mul_lt_mul_of_pos_right hn (pow_pos hnpos (8*K+5))
    simpa only [show 8*K+6=(8*K+5)+1 by omega,pow_succ,mul_comm] using hh
  by_contra hz
  have hp : 1≤value^4 := Nat.one_le_pow 4 value (Nat.pos_of_ne_zero hz)
  have hm := Nat.mul_le_mul_left (M^(r*(4*K+3))) hp
  simp only [mul_one] at hm
  omega
end ThreeSum.TernaryPairedBudgetSelector
