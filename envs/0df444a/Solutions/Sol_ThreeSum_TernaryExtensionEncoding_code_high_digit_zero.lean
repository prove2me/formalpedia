-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.code_high_digit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:06.103908+00:00
-- url     : https://prove2.me/submissions/fa02caa2-63bb-4634-8f70-9ad87eb1281e

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d code k : ℕ} (hc : code<p^d) (hk : d≤k) :
    code/p^k%p=0 := by
  have hpow : p^d≤p^k := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).one_lt; omega) hk
  rw [Nat.div_eq_of_lt (hc.trans_le hpow)]
  simp
end ThreeSum.TernaryExtensionEncoding
