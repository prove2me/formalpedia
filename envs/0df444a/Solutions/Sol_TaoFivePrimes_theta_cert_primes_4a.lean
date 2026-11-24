-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4a
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:21.115307+00:00
-- url     : https://prove2.me/submissions/7b832e9e-6c39-4c17-83a3-8c11fae1406d

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 978 1033).filter Nat.Prime = ({ 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 978 1033).filter Nat.Prime = ({ 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033 } : Finset ℕ) :=
  TaoFivePrimes.solution
