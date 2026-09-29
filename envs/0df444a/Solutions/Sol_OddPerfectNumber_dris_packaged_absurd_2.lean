-- Prove2me | solution 2 for OddPerfectNumber.dris_packaged_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T06:31:52.19383+00:00
-- url     : https://prove2.me/submissions/a231c997-6bfa-4397-b079-7188526b7f2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_cofactor_dvd
import Theorems.Thm_OddPerfectNumber_dris_packaged_core

open OddPerfectNumber

-- Reduction of the general Dris packaged absurdity: m^2 = t * d with m odd
-- forces d odd, and 2 * m^2 = sigma(p^k) * d then feeds the shared
-- (proved) cofactor lemma to yield d | m^2, isolating the research core.
-- Staged; submitted only after the core child is PUBLISHED.
theorem solution (p k m s t d : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_odd : Odd s)
    (hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d) : False := by
  have hm2odd : Odd (m ^ 2) := hm.pow
  have hd_odd : Odd d := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    have hev : Even (m ^ 2) := by
      rw [hdvd]
      exact h.mul_left t
    exact (Nat.not_even_iff_odd.mpr hm2odd) hev
  have hpack2 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * d := by
    rw [hsig, hdvd]
    ring
  have hd_dvd : d ∣ m ^ 2 :=
    dris_cofactor_dvd m d (∑ d ∈ (p ^ k).divisors, d) hd_odd hpack2
  exact dris_packaged_core p k m s t d hp hm hpm hs_odd hsig hdvd hsigm hd_dvd
