-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_clbZ_le_log
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:21:25.708424+00:00
-- url     : https://prove2.me/submissions/4012c1ef-7d61-45aa-83e1-796f336e5333

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_log_1
import Theorems.Thm_TaoFivePrimes_theta_cert_log_2
import Theorems.Thm_TaoFivePrimes_theta_cert_log_3
import Theorems.Thm_TaoFivePrimes_theta_cert_log_4
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution (p : ℕ) (hp : p ∈ plist) :
    ((clbZ p : ℕ) : ℝ) ≤ Real.log p * 10 ^ 4 := by
  have hmem := hp
  simp only [plist, Finset.mem_union, or_assoc] at hmem
  rcases hmem with h | h | h | h
  · exact le_of_lt (theta_cert_log_1 p h)
  · exact le_of_lt (theta_cert_log_2 p h)
  · exact le_of_lt (theta_cert_log_3 p h)
  · exact le_of_lt (theta_cert_log_4 p h)

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (p : ℕ) (hp : p ∈ plist) :
    ((clbZ p : ℕ) : ℝ) ≤ Real.log p * 10 ^ 4 :=
  TaoFivePrimes.solution p hp
