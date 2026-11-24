-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_3
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:38.881254+00:00
-- url     : https://prove2.me/submissions/b80a1b64-da9f-4c27-a8c3-a6189b503dfd

import Theorems.Thm_TaoFivePrimes_theta_cert_primes_3a
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_3b
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_3c
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_3d
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 602 977).filter Nat.Prime = plist3 := by
  have hIcc : (Finset.Icc 602 977 : Finset ℕ) =
      Finset.Icc 602 695 ∪ Finset.Icc 696 789 ∪ Finset.Icc 790 883 ∪ Finset.Icc 884 977 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hIcc, Finset.filter_union, Finset.filter_union, Finset.filter_union, theta_cert_primes_3a, theta_cert_primes_3b, theta_cert_primes_3c, theta_cert_primes_3d]
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 602 977).filter Nat.Prime = plist3 :=
  TaoFivePrimes.solution
