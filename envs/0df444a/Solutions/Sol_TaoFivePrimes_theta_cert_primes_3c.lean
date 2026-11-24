-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_3c
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:17.291956+00:00
-- url     : https://prove2.me/submissions/9d2841fb-52cb-4d9f-96f6-dde9f6d2e170

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 790 883).filter Nat.Prime = ({ 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 790 883).filter Nat.Prime = ({ 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883 } : Finset ℕ) :=
  TaoFivePrimes.solution
