-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_4
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:40.461413+00:00
-- url     : https://prove2.me/submissions/ca736680-3aab-4c9e-96e1-dd56787c93b5

import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4a
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4b
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4c
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4d
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4e
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4f
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4g
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_4h
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 978 1420).filter Nat.Prime = plist4 := by
  have hIcc : (Finset.Icc 978 1420 : Finset ℕ) =
      Finset.Icc 978 1033 ∪ Finset.Icc 1034 1088 ∪ Finset.Icc 1089 1144 ∪ Finset.Icc 1145 1199 ∪ Finset.Icc 1200 1255 ∪ Finset.Icc 1256 1310 ∪ Finset.Icc 1311 1365 ∪ Finset.Icc 1366 1420 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hIcc, Finset.filter_union, Finset.filter_union, Finset.filter_union, Finset.filter_union, Finset.filter_union, Finset.filter_union, Finset.filter_union, theta_cert_primes_4a, theta_cert_primes_4b, theta_cert_primes_4c, theta_cert_primes_4d, theta_cert_primes_4e, theta_cert_primes_4f, theta_cert_primes_4g, theta_cert_primes_4h]
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 978 1420).filter Nat.Prime = plist4 :=
  TaoFivePrimes.solution
