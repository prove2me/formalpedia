-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_1
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:35.696221+00:00
-- url     : https://prove2.me/submissions/b3711f22-fc6f-42ef-8d1c-81b2d7d81884

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 2 257).filter Nat.Prime = plist1 := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 2 257).filter Nat.Prime = plist1 :=
  TaoFivePrimes.solution
