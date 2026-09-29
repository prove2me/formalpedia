-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D37_source_length
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:59:39.347734+00:00
-- url     : https://prove2.me/submissions/a27d16f1-6742-42c9-bdd4-0e4de38801cb

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd
import Theorems.Thm_OddPerfectNumber_order_37_mod_73_eq_9_v2

theorem solution (e : Nat)
    (hdiv : 73 ∣ ∑ i ∈ Finset.range (2 * e + 1), 37 ^ i) :
    9 ∣ 2 * e + 1 := by
  have horder := OddPerfectNumber.geom_sum_dvd_implies_order_dvd hdiv
  change orderOf (37 : ZMod 73) ∣ 2 * e + 1 at horder
  rw [OddPerfectNumber.order_37_mod_73_eq_9_v2] at horder
  exact horder
