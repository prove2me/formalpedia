-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4c
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:22.810102+00:00
-- url     : https://prove2.me/submissions/02b540b5-364e-4c70-89f2-e1f5329adda1

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1089 1144).filter Nat.Prime = ({ 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1089 1144).filter Nat.Prime = ({ 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129 } : Finset ℕ) :=
  TaoFivePrimes.solution
