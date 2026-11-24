-- Prove2me | solution 1 for TaoFivePrimes.tao_totient_cert_h_check
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T20:46:43.068726+00:00
-- url     : https://prove2.me/submissions/f94323ad-2800-4861-868b-5f6d57cf898d

import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_totient_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace TaoFivePrimes

/-- The certificate inequality `R_m * A_lo + c / R_m > Q_m` at the primorial
sample points `4 <= m <= 65`, with `A_lo = 178107237/10^8` a certified lower
bound for `exp gamma` and `c = 250637/10^5`. -/
theorem solution (m : ℕ) (hm : m ∈ Finset.Icc 4 65) :
    (rll m : ℚ) * (178107237 / 10^8) + (250637 / 10^5) / (rll m) > Qpt m := by
  rw [Finset.mem_Icc] at hm
  obtain ⟨h1, h2⟩ := hm
  interval_cases m <;> norm_num [rll, Qpt, Pnum, Pden]

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (m : ℕ) (hm : m ∈ Finset.Icc 4 65) :
    (rll m : ℚ) * (178107237 / 10^8) + (250637 / 10^5) / (rll m) > Qpt m :=
  TaoFivePrimes.solution m hm

#print axioms solution
