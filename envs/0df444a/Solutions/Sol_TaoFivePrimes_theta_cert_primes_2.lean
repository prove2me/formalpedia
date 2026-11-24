-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_primes_2
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:37.193446+00:00
-- url     : https://prove2.me/submissions/5dab197f-d7cd-45a7-a889-b52e64d20067

import Theorems.Thm_TaoFivePrimes_theta_cert_primes_2a
import Theorems.Thm_TaoFivePrimes_theta_cert_primes_2b
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

theorem solution : (Finset.Icc 258 601).filter Nat.Prime = plist2 := by
  have hIcc : (Finset.Icc 258 601 : Finset ℕ) =
      Finset.Icc 258 429 ∪ Finset.Icc 430 601 := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hIcc, Finset.filter_union, theta_cert_primes_2a, theta_cert_primes_2b]
  decide

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (Finset.Icc 258 601).filter Nat.Prime = plist2 :=
  TaoFivePrimes.solution
