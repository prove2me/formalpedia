-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T18:44:40.378969+00:00
-- url     : https://prove2.me/submissions/4ec305c9-ce57-49b9-bfaf-fe9485148c92

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_candidates

theorem solution (D p q4 : Nat)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 19531 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D) :
    False := by
  have hc := OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_candidates
    D p q4 hDlow hDhigh hp hp4 hp_eq hq4 (by omega) hq4le hq4dvd
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 <;>
    omega
