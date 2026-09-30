-- Prove2me | solution 1 for TranscendenceTheory.formal_quadratic_spectrum_factorization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T23:33:07.460987+00:00
-- url     : https://prove2.me/submissions/c741e820-494a-4014-96fb-5be5bea4ba34

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

private lemma split_quadratic {S : Type*} [CommRing S] [IsDomain S]
    (a b d y z : S) (hy : y ^ 2 = d) :
    z ^ 2 - 2 * a * z + (a ^ 2 - d * b ^ 2) = 0 ↔
      z = a + y * b ∨ z = a - y * b := by
  have hfactor : z ^ 2 - 2 * a * z + (a ^ 2 - d * b ^ 2) =
      (z - (a + y * b)) * (z - (a - y * b)) := by
    rw [← hy]
    ring
  rw [hfactor, mul_eq_zero]
  simp only [sub_eq_zero]

theorem solution
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (A B D Y : PowerSeries R) (hY : Y ^ 2 = D) (z : S) :
    z ^ 2 - f (PowerSeries.coeff 0 (2 * A)) * z +
        f (PowerSeries.coeff 0 (A ^ 2 - D * B ^ 2)) = 0 ↔
      z = f (PowerSeries.coeff 0 (A + Y * B)) ∨
        z = f (PowerSeries.coeff 0 (A - Y * B)) := by
  let θ : PowerSeries R →+* S := f.comp PowerSeries.constantCoeff
  have hy : θ Y ^ 2 = θ D := by rw [← map_pow, hY]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  change z ^ 2 - θ (2 * A) * z + θ (A ^ 2 - D * B ^ 2) = 0 ↔
    z = θ (A + Y * B) ∨ z = θ (A - Y * B)
  simpa only [map_mul, map_ofNat, map_pow, map_sub, map_add] using
    split_quadratic (θ A) (θ B) (θ D) (θ Y) z hy
