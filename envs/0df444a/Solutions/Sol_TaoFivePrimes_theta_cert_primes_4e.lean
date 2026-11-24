-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4e
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:24.067456+00:00
-- url     : https://prove2.me/submissions/d4497231-687c-4fb2-a2a7-704f6d0bae39

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1200 1255).filter Nat.Prime = ({ 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1200 1255).filter Nat.Prime = ({ 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249 } : Finset ℕ) :=
  TaoFivePrimes.solution
