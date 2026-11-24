-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:41:08.521712+00:00
-- url     : https://prove2.me/submissions/1b7113dc-9d2d-427b-8347-6a0e45bad5d5

import Mathlib
open MvPolynomial


theorem solution {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (f : R →+* S) (w : σ → M) {p : MvPolynomial σ R} {b : M}
    (hp : IsWeightedHomogeneous w p b) : IsWeightedHomogeneous w (MvPolynomial.map f p) b := by
  intro d hd; apply hp; intro hz; apply hd; simp [MvPolynomial.coeff_map,hz]
