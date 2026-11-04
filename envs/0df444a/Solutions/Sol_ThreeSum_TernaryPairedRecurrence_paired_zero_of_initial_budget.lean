-- Prove2me | solution 1 for ThreeSum.TernaryPairedRecurrence.paired_zero_of_initial_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:04.200197+00:00
-- url     : https://prove2.me/submissions/2ecc7045-20d5-4aae-b050-506e826ac0de

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Theorems.Thm_ThreeSum_TernaryPairedRecurrence_paired_fourth_power_bound

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence
namespace ThreeSum.TernaryPairedRecurrence
theorem _root_.solution (K M a b n C : ℕ) (ha : 0<a)
    (score : ℕ → ℕ) (hstep : ∀ j, a*score (j+1)≤b*score j)
    (hbudget : b^4*M^(4*K+3)≤a^4) (r : ℕ)
    (hcover : n^2≤M^r) (hinit : (score 0)^4≤C*n^(8*K+5)) (hn : C<n) :
    score r=0 := by
  have hnpos : 0<n := by omega
  have hbound := paired_fourth_power_bound K M a b ha score hstep hbudget r
  have hbase : n^(8*K+6)≤M^(r*(4*K+3)) := by
    have hh := Nat.pow_le_pow_left hcover (4*K+3)
    simpa only [←pow_mul,show 2*(4*K+3)=8*K+6 by ring] using hh
  have hstrict : C*n^(8*K+5)<n^(8*K+6) := by
    have hh := Nat.mul_lt_mul_of_pos_right hn (pow_pos hnpos (8*K+5))
    convert hh using 1 <;> rw [show 8*K+6=(8*K+5)+1 by omega,pow_succ] <;> ring
  by_contra hz
  have hp : 1≤(score r)^4 := Nat.one_le_pow 4 (score r) (Nat.pos_of_ne_zero hz)
  have hm := Nat.mul_le_mul_left (M^(r*(4*K+3))) hp
  simp only [mul_one] at hm
  omega
end ThreeSum.TernaryPairedRecurrence
