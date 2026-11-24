-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_3a
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:15.829004+00:00
-- url     : https://prove2.me/submissions/d495f9d5-31ac-4531-ae38-f185d81d9cab

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 602 695).filter Nat.Prime = ({ 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 602 695).filter Nat.Prime = ({ 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691 } : Finset ℕ) :=
  TaoFivePrimes.solution
