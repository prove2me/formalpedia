-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_multiplication_drazin_inverse
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T01:44:18.052852+00:00
-- url     : https://prove2.me/submissions/bfcec9f8-9d42-483d-9141-ea46e3907d6b

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

noncomputable section


theorem solution
    (A : Type*) [CommRing A] (I J R : Ideal A) (d : ℕ) (p : A)
    (hsum : J ⊔ R = ⊤) (hinf : J ⊓ R = I)
    (hnil : (Ideal.Quotient.mk J p) ^ d = 0)
    (hunit : IsUnit (Ideal.Quotient.mk R p)) :
    ∃! b : A ⧸ I,
      Ideal.Quotient.mk I p * b * b = b ∧
      (Ideal.Quotient.mk I p) ^ (d + 1) * b = (Ideal.Quotient.mk I p) ^ d := by
  classical
  subst I
  let E := Ideal.quotientInfEquivQuotientProd J R (Ideal.isCoprime_iff_sup_eq.mpr hsum)
  let a := Ideal.Quotient.mk (J ⊓ R) p
  have hEa : E a = (Ideal.Quotient.mk J p, Ideal.Quotient.mk R p) := by
    apply Prod.ext <;> simp only [E, a,
      Ideal.quotientInfEquivQuotientProd_fst, Ideal.quotientInfEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
  obtain ⟨u, hu⟩ := hunit
  have hinv : Ideal.Quotient.mk R p * (↑u⁻¹ : A ⧸ R) = 1 := by
    rw [← hu]
    exact u.mul_inv
  let b := E.symm (0, (↑u⁻¹ : A ⧸ R))
  have hb : E b = (0, (↑u⁻¹ : A ⧸ R)) := E.apply_symm_apply _
  change ∃! b, a * b * b = b ∧ a ^ (d + 1) * b = a ^ d
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · apply E.injective
    simp only [map_mul, hEa, hb, Prod.mk_mul_mk]
    exact Prod.ext (by simp) (by rw [hinv, one_mul])
  · apply E.injective
    simp only [map_mul, map_pow, hEa, hb]
    apply Prod.ext
    · change (Ideal.Quotient.mk J p) ^ (d + 1) * 0 = (Ideal.Quotient.mk J p) ^ d
      rw [mul_zero, hnil]
    · change (Ideal.Quotient.mk R p) ^ (d + 1) * (↑u⁻¹ : A ⧸ R) =
        (Ideal.Quotient.mk R p) ^ d
      rw [pow_succ, mul_assoc, hinv, mul_one]
  · intro c hc
    have hcJ : Ideal.Quotient.mk J p * (E c).1 * (E c).1 = (E c).1 := by
      simpa only [map_mul, hEa, Prod.fst_mul] using
        congrArg (fun x => (E x).1) hc.1
    have hcR : (Ideal.Quotient.mk R p) ^ (d + 1) * (E c).2 =
        (Ideal.Quotient.mk R p) ^ d := by
      simpa only [map_mul, map_pow, hEa, Prod.snd_mul, Prod.pow_snd] using
        congrArg (fun x => (E x).2) hc.2
    have hcJzero : (E c).1 = 0 := by
      have hnilc : IsNilpotent (Ideal.Quotient.mk J p * (E c).1) :=
        (Commute.all _ _).isNilpotent_mul_right ⟨d, hnil⟩
      apply hnilc.isUnit_one_sub.mul_right_cancel
      rw [zero_mul]
      calc
        (E c).1 * (1 - Ideal.Quotient.mk J p * (E c).1) =
            (E c).1 - Ideal.Quotient.mk J p * (E c).1 * (E c).1 := by ring
        _ = 0 := by rw [hcJ, sub_self]
    have hcRinv : (E c).2 = (↑u⁻¹ : A ⧸ R) := by
      apply ((show IsUnit (Ideal.Quotient.mk R p) from ⟨u, hu⟩).pow (d + 1)).mul_left_cancel
      rw [hcR, pow_succ, mul_assoc, hinv, mul_one]
    apply E.injective
    rw [hb]
    exact Prod.ext hcJzero hcRinv

