-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4f
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:01:26.135991+00:00
-- url     : https://prove2.me/submissions/ba7f78bf-55ef-4e0f-9a95-aef86b34830d

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 1256 1310).filter Nat.Prime = ({ 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307 } : Finset ℕ) := by
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 1256 1310).filter Nat.Prime = ({ 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307 } : Finset ℕ) :=
  TaoFivePrimes.solution
