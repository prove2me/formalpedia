-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_3b
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:16.496195+00:00
-- url     : https://prove2.me/submissions/e01643d3-f5d6-4827-9e00-af0615fb2b70

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 696 789).filter Nat.Prime = ({ 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 696 789).filter Nat.Prime = ({ 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787 } : Finset ℕ) :=
  TaoFivePrimes.solution
