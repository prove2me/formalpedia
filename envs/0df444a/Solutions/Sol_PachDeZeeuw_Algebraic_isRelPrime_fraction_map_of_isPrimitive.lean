-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.isRelPrime_fraction_map_of_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:54.795823+00:00
-- url     : https://prove2.me/submissions/7c3467f8-d25c-41ae-a2e8-7103842f7139

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hQprim : Q.IsPrimitive)
    (hrel : IsRelPrime P Q) :
    IsRelPrime (P.map (algebraMap XCoeff XFrac))
               (Q.map (algebraMap XCoeff XFrac)) := by
  intro D hDP hDQ
  by_cases hD : D = 0
  · have hPQ0 : P ≠ 0 ∧ Q ≠ 0 := ⟨hPprim.ne_zero, hQprim.ne_zero⟩
    have hmap_inj : Function.Injective (Polynomial.map (algebraMap XCoeff XFrac)) :=
      Polynomial.map_injective _ (IsFractionRing.injective XCoeff XFrac)
    have hmapQ0 : Q.map (algebraMap XCoeff XFrac) ≠ 0 := by
      intro hzero
      have hzero' : Polynomial.map (algebraMap XCoeff XFrac) Q =
          Polynomial.map (algebraMap XCoeff XFrac) 0 := by
        simpa using hzero
      exact hPQ0.2 (hmap_inj hzero')
    have hzero : Q.map (algebraMap XCoeff XFrac) = 0 := by
      simpa [hD] using hDQ
    exact (hmapQ0 hzero).elim
  · rcases IsLocalization.integerNormalization_spec (nonZeroDivisors XCoeff) D with
      ⟨b, hb, hnorm⟩
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hb0' : (algebraMap XCoeff XFrac b) ≠ 0 := by
      intro hb'
      exact hb0 (IsFractionRing.injective XCoeff XFrac (by simpa using hb'))
    have hbunit : IsUnit (Polynomial.C (algebraMap XCoeff XFrac b)) := by
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0')
    rcases hbunit with ⟨u, hu⟩
    have hassoc :
        Associated D (Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D)) := by
      have hnorm' :
          Polynomial.map (algebraMap XCoeff XFrac)
            (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) =
          (algebraMap XCoeff XFrac b) • D := by
        simpa using hnorm
      have hnorm'' :
          Polynomial.map (algebraMap XCoeff XFrac)
            (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) =
          Polynomial.C ((algebraMap XCoeff XFrac) b) * D := by
        rw [← Polynomial.smul_eq_C_mul]
        exact hnorm'
      refine ⟨u, ?_⟩
      rw [hu]
      calc
        D * Polynomial.C ((algebraMap XCoeff XFrac) b) =
            Polynomial.C ((algebraMap XCoeff XFrac) b) * D := by
              simp [mul_comm]
        _ = Polynomial.map (algebraMap XCoeff XFrac)
              (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) := hnorm''.symm
    have hnorm_dvdP :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) ∣
        P.map (algebraMap XCoeff XFrac) := by
      exact (hassoc.dvd_iff_dvd_left).1 hDP
    have hnorm_dvdQ :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) ∣
        Q.map (algebraMap XCoeff XFrac) := by
      exact (hassoc.dvd_iff_dvd_left).1 hDQ
    have hprim_dvd_norm :
        (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D := by
      exact Polynomial.primPart_dvd _
    have hmap_prim_dvd_norm :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) := by
      let A : Polynomial XCoeff :=
        IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D
      let B : Polynomial XCoeff := A.primPart
      have hprim_dvd_A : B ∣ A := by
        exact Polynomial.primPart_dvd A
      rcases hprim_dvd_A with ⟨r, hr⟩
      refine ⟨Polynomial.map (algebraMap XCoeff XFrac) r, ?_⟩
      calc
        Polynomial.map (algebraMap XCoeff XFrac)
            (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) =
            Polynomial.map (algebraMap XCoeff XFrac) A := by
          rfl
        _ =
            Polynomial.map (algebraMap XCoeff XFrac) (B * r) := by
          rw [hr]
        _ =
            Polynomial.map (algebraMap XCoeff XFrac) B *
            Polynomial.map (algebraMap XCoeff XFrac) r := by
          rw [Polynomial.map_mul]
        _ =
            Polynomial.map (algebraMap XCoeff XFrac)
              (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart *
            Polynomial.map (algebraMap XCoeff XFrac) r := by
          rfl
    have hmap_prim_dvd_P :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        P.map (algebraMap XCoeff XFrac) := dvd_trans hmap_prim_dvd_norm hnorm_dvdP
    have hmap_prim_dvd_Q :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        Q.map (algebraMap XCoeff XFrac) := dvd_trans hmap_prim_dvd_norm hnorm_dvdQ
    have hprim_dvd_P :
        (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣ P := by
      exact
        Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
          (K := XFrac)
          (p := (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart)
          (q := P)
          (Polynomial.isPrimitive_primPart _)
          hmap_prim_dvd_P
    have hprim_dvd_Q :
        (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣ Q := by
      exact
        Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
          (K := XFrac)
          (p := (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart)
          (q := Q)
          (Polynomial.isPrimitive_primPart _)
          hmap_prim_dvd_Q
    have hunit_prim :
        IsUnit (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart :=
      hrel hprim_dvd_P hprim_dvd_Q
    exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hD hunit_prim
