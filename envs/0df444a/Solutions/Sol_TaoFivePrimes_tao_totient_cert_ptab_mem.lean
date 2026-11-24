-- Prove2me | solution 1 for TaoFivePrimes.tao_totient_cert_ptab_mem
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T20:46:37.623779+00:00
-- url     : https://prove2.me/submissions/ca9267b7-5f4d-4235-8066-a56b46c0623a

import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Definitions.Def_TaoFivePrimes_totient_cert_tables
import Mathlib.Tactic
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TaoFivePrimes

/-- Each entry of the certificate prime table `ptab` is one of the 66 primes of `plist`. -/
theorem solution (i : ℕ) (hi : i < 66) : ptab i ∈ plist := by
  interval_cases i <;> decide

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (i : ℕ) (hi : i < 66) : TaoFivePrimes.ptab i ∈ TaoFivePrimes.plist :=
  TaoFivePrimes.solution i hi

#print axioms solution
