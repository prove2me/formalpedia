-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_plist_eq
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:42.241096+00:00
-- url     : https://prove2.me/submissions/fa7af07a-c19f-4501-b6d4-e5c48e7b1a88

import Theorems.Thm_TaoFivePrimes_theta_cert_primes_1
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_2
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_3
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4
set_option maxRecDepth 1000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 2 1420).filter Nat.Prime = plist := by
  have hIcc : (Finset.Icc 2 1420 : Finset ℕ) =
      Finset.Icc 2 257 ∪ Finset.Icc 258 601 ∪ Finset.Icc 602 977 ∪ Finset.Icc 978 1420 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hIcc, Finset.filter_union, Finset.filter_union, Finset.filter_union,
    theta_cert_primes_1, theta_cert_primes_2, theta_cert_primes_3, theta_cert_primes_4]
  rfl

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 2 1420).filter Nat.Prime = plist :=
  TaoFivePrimes.solution
