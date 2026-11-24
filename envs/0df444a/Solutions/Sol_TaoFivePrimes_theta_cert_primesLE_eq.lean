-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primesLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:21:25.126629+00:00
-- url     : https://prove2.me/submissions/f27091b5-e4a3-491f-a92a-4f628d938476

import Mathlib.NumberTheory.PrimeCounting
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_plist_eq
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution (n : ℕ) (hn : n ≤ 1420) :
    Nat.primesLE n = plist.filter (· ≤ n) := by
  have h1 : Nat.primesLE n = (Finset.Icc 2 1420).filter (fun p => Nat.Prime p ∧ p ≤ n) := by
    rw [Nat.primesLE_eq_filter_range]
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hpn, hp⟩
      exact ⟨⟨hp.two_le, (Nat.lt_succ_iff.mp hpn).trans hn⟩, hp, Nat.lt_succ_iff.mp hpn⟩
    · rintro ⟨⟨-, -⟩, hp, hpn⟩
      exact ⟨Nat.lt_succ_iff.mpr hpn, hp⟩
  rw [h1, ← theta_cert_plist_eq, ← Finset.filter_filter]

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n : ℕ) (hn : n ≤ 1420) :
    Nat.primesLE n = plist.filter (· ≤ n) :=
  TaoFivePrimes.solution n hn
