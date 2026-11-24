-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4h
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:28.18341+00:00
-- url     : https://prove2.me/submissions/1552178c-1d9d-40ba-be6e-408b8dcf31d6

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1366 1420).filter Nat.Prime = ({ 1367, 1373, 1381, 1399, 1409 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1366 1420).filter Nat.Prime = ({ 1367, 1373, 1381, 1399, 1409 } : Finset ℕ) :=
  TaoFivePrimes.solution
