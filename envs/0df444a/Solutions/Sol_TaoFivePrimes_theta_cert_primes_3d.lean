-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_3d
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:19.752975+00:00
-- url     : https://prove2.me/submissions/afd4e705-3403-496c-8184-e220b868e15d

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 884 977).filter Nat.Prime = ({ 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 884 977).filter Nat.Prime = ({ 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977 } : Finset ℕ) :=
  TaoFivePrimes.solution
