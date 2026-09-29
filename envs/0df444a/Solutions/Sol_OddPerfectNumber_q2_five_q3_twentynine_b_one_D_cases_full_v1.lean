-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_full_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:07:18.823977+00:00
-- url     : https://prove2.me/submissions/06a03ce3-f696-4ab0-a72e-c1d32d53b26e

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_loa_v3
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_lob_v3
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_mid_v3
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_hi_v3

open OddPerfectNumber

theorem solution (D : Nat)
    (hlo : 12 ≤ D) (hhi : D ≤ 105)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  by_cases h1 : D ≤ 27
  · exact q2_five_q3_twentynine_b_one_D_cases_loa_v3 D hlo h1 hD hp
  · by_cases h2 : D ≤ 43
    · have hlo2 : 28 ≤ D := by omega
      exact q2_five_q3_twentynine_b_one_D_cases_lob_v3 D hlo2 h2 hD hp
    · by_cases h3 : D ≤ 74
      · have hlo3 : 44 ≤ D := by omega
        exact q2_five_q3_twentynine_b_one_D_cases_mid_v3 D hlo3 h3 hD hp
      · have hlo4 : 75 ≤ D := by omega
        exact q2_five_q3_twentynine_b_one_D_cases_hi_v3 D hlo4 hhi hD hp
