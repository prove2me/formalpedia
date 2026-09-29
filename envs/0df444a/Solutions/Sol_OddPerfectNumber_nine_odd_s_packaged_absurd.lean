-- Prove2me | solution 1 for OddPerfectNumber.nine_odd_s_packaged_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:20:22.44492+00:00
-- url     : https://prove2.me/submissions/a07ca020-ad3c-4e06-873d-28916386a391
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_packaged_absurd

open OddPerfectNumber

-- Specialization reduction: the k = 9 packaged absurdity is the general
-- Dris packaged absurdity at k := 9. One exact application; the unused
-- nine-specific hypotheses (p ≠ 2, p % 4 = 1) simply do not feature.
theorem solution (p m s t d : Nat)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hs_odd : Odd s)
    (hsig9 : (∑ d ∈ (p ^ 9).divisors, d) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p ^ 9 * d) : False :=
  dris_packaged_absurd p 9 m s t d hp hm hpm hs_odd hsig9 hdvd hsig
