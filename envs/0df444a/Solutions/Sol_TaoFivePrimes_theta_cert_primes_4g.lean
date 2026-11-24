-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4g
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:26.88078+00:00
-- url     : https://prove2.me/submissions/4d1a3e7c-f926-48af-9144-facf6279d3c9

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1311 1365).filter Nat.Prime = ({ 1319, 1321, 1327, 1361 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1311 1365).filter Nat.Prime = ({ 1319, 1321, 1327, 1361 } : Finset ℕ) :=
  TaoFivePrimes.solution
