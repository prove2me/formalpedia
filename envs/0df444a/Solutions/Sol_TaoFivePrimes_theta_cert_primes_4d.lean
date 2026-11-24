-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4d
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:23.5054+00:00
-- url     : https://prove2.me/submissions/cec26009-a04b-4e8b-9d8e-9f000c7524e8

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1145 1199).filter Nat.Prime = ({ 1151, 1153, 1163, 1171, 1181, 1187, 1193 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1145 1199).filter Nat.Prime = ({ 1151, 1153, 1163, 1171, 1181, 1187, 1193 } : Finset ℕ) :=
  TaoFivePrimes.solution
