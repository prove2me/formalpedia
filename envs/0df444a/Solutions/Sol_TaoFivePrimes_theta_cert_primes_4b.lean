-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4b
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:22.268364+00:00
-- url     : https://prove2.me/submissions/efa0b1ce-412e-43f7-b43b-332cbfbc0123

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1034 1088).filter Nat.Prime = ({ 1039, 1049, 1051, 1061, 1063, 1069, 1087 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1034 1088).filter Nat.Prime = ({ 1039, 1049, 1051, 1061, 1063, 1069, 1087 } : Finset ℕ) :=
  TaoFivePrimes.solution
