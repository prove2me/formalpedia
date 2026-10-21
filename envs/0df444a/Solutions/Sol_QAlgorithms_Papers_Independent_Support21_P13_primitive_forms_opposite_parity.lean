-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.primitive_forms_opposite_parity
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T04:50:35.356341+00:00
-- url     : https://prove2.me/submissions/c7a0ad2f-93e2-4748-a61f-0cfa21c22bc6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith


open QAlgorithms.Papers.Independent.Support21.P13

namespace CTCyclotomic

theorem omega_pow_four : (QAlgorithms.gateT true true) ^ 4 = -1 := by
  change Complex.exp (Complex.I * Real.pi / 4) ^ 4 = -1
  rw [← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (4 : ℂ) * (Complex.I * Real.pi / 4) = (Real.pi : ℂ) * Complex.I := by ring
  rw [he, Complex.exp_pi_mul_I]

theorem coordinateValue_mem (a : Fin 4 → ℤ) : coordinateValue a ∈ integralRing := by
  have hw : QAlgorithms.gateT true true ∈ integralRing :=
    Subring.subset_closure (by simp)
  unfold coordinateValue
  exact integralRing.add_mem
    (integralRing.add_mem
      (integralRing.add_mem (intCast_mem integralRing (a 0))
        (integralRing.mul_mem (intCast_mem integralRing (a 1)) hw))
      (integralRing.mul_mem (intCast_mem integralRing (a 2)) (integralRing.pow_mem hw 2)))
    (integralRing.mul_mem (intCast_mem integralRing (a 3)) (integralRing.pow_mem hw 3))

theorem sqrtTwo_mul_coordinateValue (b : Fin 4 → ℤ) :
    ((QAlgorithms.gateT true true) - (QAlgorithms.gateT true true) ^ 3) * coordinateValue b =
      coordinateValue (![b 1 - b 3, b 0 + b 2, b 1 + b 3, b 2 - b 0]) := by
  have hw5 : (QAlgorithms.gateT true true) ^ 5 = -(QAlgorithms.gateT true true) := by
    rw [show (5 : ℕ) = 4 + 1 by decide, pow_add, pow_one, omega_pow_four]
    ring
  have hw6 : (QAlgorithms.gateT true true) ^ 6 = -(QAlgorithms.gateT true true) ^ 2 := by
    rw [show (6 : ℕ) = 4 + 2 by decide, pow_add, omega_pow_four]
    ring
  simp only [coordinateValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  push_cast
  ring_nf
  rw [omega_pow_four, hw5, hw6]
  ring

theorem sqrtTwoInteger_mul_coordinateValue (b : Fin 4 → ℤ) :
    (sqrtTwoInteger : ℂ) * coordinateValue b =
      coordinateValue (![b 1 - b 3, b 0 + b 2, b 1 + b 3, b 2 - b 0]) := by
  exact sqrtTwo_mul_coordinateValue b


end CTCyclotomic



set_option autoImplicit false

noncomputable section
open scoped Classical
open QAlgorithms.Papers.Independent.Support21.P13

namespace CTPrimitiveFormsParity

/-- The parity of the two quadratic forms depends only on the two sums of
opposite coefficients. If these sums are not both even, the forms have
opposite parity. -/
theorem forms_parity (a0 a1 a2 a3 : ℤ)
    (h : ¬ (Even (a0 + a2) ∧ Even (a1 + a3))) :
    (Even (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) ∧
      Odd (a0 * (a1 - a3) + a2 * (a1 + a3))) ∨
    (Odd (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) ∧
      Even (a0 * (a1 - a3) + a2 * (a1 + a3))) := by
  rcases Int.even_or_odd a0 with h0 | h0 <;>
  rcases Int.even_or_odd a1 with h1 | h1 <;>
  rcases Int.even_or_odd a2 with h2 | h2 <;>
  rcases Int.even_or_odd a3 with h3 | h3 <;>
  simp_all [← Int.not_even_iff_odd, parity_simps]

/-- If both opposite coefficient sums are even, division by sqrt(2) has an
explicit cyclotomic integer quotient. -/
theorem sqrtTwo_dvd_of_even_pairs (a : Fin 4 → ℤ)
    (he : Even (a 0 + a 2) ∧ Even (a 1 + a 3)) :
    sqrtTwoInteger ∣ (⟨coordinateValue a, CTCyclotomic.coordinateValue_mem a⟩ : integralRing) := by
  rcases he with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  let b : Fin 4 → ℤ := ![v - a 3, u, v, u - a 0]
  have hc : (![b 1 - b 3, b 0 + b 2, b 1 + b 3, b 2 - b 0] : Fin 4 → ℤ) = a := by
    funext i
    fin_cases i <;> simp only [b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] <;> linarith
  refine ⟨⟨coordinateValue b, CTCyclotomic.coordinateValue_mem b⟩, ?_⟩
  apply Subtype.ext
  change coordinateValue a = (sqrtTwoInteger : ℂ) * coordinateValue b
  simpa only [hc] using (CTCyclotomic.sqrtTwoInteger_mul_coordinateValue b).symm

end CTPrimitiveFormsParity

/-- Proposition 3 of Kliuchnikov, Maslov and Mosca, Appendix A: primitive
cyclotomic numerators have quadratic forms of opposite parity. -/
theorem solution (a : Fin 4 → ℤ)
    (hprimitive : gde (coordinateValue a) = 0) :
    (Even (formP a) ∧ Odd (formQ a)) ∨
      (Odd (formP a) ∧ Even (formQ a)) := by
  have hnot : ¬ (Even (a 0 + a 2) ∧ Even (a 1 + a 3)) := by
    intro he
    rw [gde, dif_pos (CTCyclotomic.coordinateValue_mem a)] at hprimitive
    exact (emultiplicity_eq_zero.mp hprimitive)
      (CTPrimitiveFormsParity.sqrtTwo_dvd_of_even_pairs a he)
  simpa only [formP, formQ] using
    CTPrimitiveFormsParity.forms_parity (a 0) (a 1) (a 2) (a 3) hnot

#print axioms solution
