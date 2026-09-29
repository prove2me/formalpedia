-- Prove2me | solution 3 for OddPerfectNumber.dris_packaged_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:15:21.949256+00:00
-- url     : https://prove2.me/submissions/66779e55-242e-4514-a863-b9264c717dd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_packaged_core

theorem _root_.solution (p k m s t d : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_odd : Odd s)
    (hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d) : False :=
  OddPerfectNumber.dris_packaged_core p k m s t d hp hm hpm hs_odd hsig hdvd hsigm
    ⟨t, by rw [hdvd]; ring⟩

#print axioms solution
