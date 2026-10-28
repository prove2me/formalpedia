-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.ancillaPurityCap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:47:02.173215+00:00
-- url     : https://prove2.me/submissions/1fd2ac2f-b5e2-416c-8f36-b377d8fd6082

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate

namespace X4P32
open QAlgorithms.Papers.Independent.Information100.P32

lemma pur (p : ℝ) (c : ℂ) : purity (rho p c) = p ^ 2 + (1 - p) ^ 2 + 2 * Complex.normSq c := by
  simp [purity, rho, Matrix.trace, Matrix.mul_apply, Complex.normSq_apply,
    Complex.mul_re]
  ring

lemma nsq (m : Model) :
    Complex.normSq (starCoherence m) =
      Complex.normSq m.cA * (2 * m.pA - 1) ^ 2 * angleS m ^ 2 * denominatorD m /
        denominatorK m ^ 2 := by
  have e : starCoherence m = -(m.cA * (((2 * m.pA - 1) * angleS m / denominatorK m : ℝ) : ℂ)) *
      ((Real.sin (m.frequency * m.duration) : ℂ) + (differenceL m : ℂ) * Complex.I) := by
    unfold starCoherence
    push_cast
    ring
  rw [e, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_add_mul_I, denominatorD]
  ring

lemma Bpos (q u C S L s co : ℝ) (hq : 0 < q) (hu : u ^ 2 ≤ 1 - 4 * q) (hCS : C ^ 2 + S ^ 2 = 1)
    (hco : co ^ 2 + s ^ 2 = 1) (hL : L = C - co) (hK : 0 < L ^ 2 + s ^ 2 - 4 * q * C * L) :
    0 < u ^ 2 * (4 * q * C ^ 2 * L ^ 2 - 2 * C * L * (L ^ 2 + s ^ 2) - S ^ 2 * (L ^ 2 + s ^ 2)) +
      (L ^ 2 + s ^ 2 - 4 * q * C * L) ^ 2 := by
  set D := L ^ 2 + s ^ 2 with hD
  set X := 4 * q * C ^ 2 * L ^ 2 - 2 * C * L * D - S ^ 2 * D with hX
  have hz : D - 2 * C * L - S ^ 2 = 0 := by
    rw [hD, hL]; nlinarith
  rcases le_or_gt 0 X with hx | hx
  · have := sq_nonneg u
    nlinarith [mul_nonneg this hx, sq_pos_of_pos hK]
  · have hD0 : 0 ≤ D := by positivity
    have hpos : 0 < C ^ 2 * L ^ 2 + S ^ 2 * D := by
      rcases (add_nonneg (by positivity : (0:ℝ) ≤ C ^ 2 * L ^ 2) (mul_nonneg (sq_nonneg S) hD0)).lt_or_eq
        with h | h
      · exact h
      · exfalso
        have h1 : C ^ 2 * L ^ 2 = 0 := by nlinarith [mul_nonneg (sq_nonneg S) hD0, sq_nonneg (C * L)]
        have h2 : S ^ 2 * D = 0 := by nlinarith [mul_nonneg (sq_nonneg S) hD0, sq_nonneg (C * L)]
        have h3 : C * L = 0 := by
          have : (C * L) ^ 2 = 0 := by rw [mul_pow]; exact h1
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        have : X = 0 := by
          rw [hX]
          have : 4 * q * C ^ 2 * L ^ 2 = 4 * q * (C * L) ^ 2 := by ring
          rw [this, h3]; nlinarith
        linarith
    have e : (1 - 4 * q) * X + (D - 4 * q * C * L) ^ 2 = D * (D - 2 * C * L - S ^ 2) +
        4 * q * (C ^ 2 * L ^ 2 + S ^ 2 * D) := by rw [hX]; ring
    rw [hz] at e
    have : (1 - 4 * q) * X ≤ u ^ 2 * X := by nlinarith
    nlinarith

lemma key (m : Model) (hK : 0 < denominatorK m) :
    purity (rho m.pA m.cA) - purity (starState m) =
      2 * Complex.normSq m.cA *
        ((2 * m.pA - 1) ^ 2 * (4 * Complex.normSq m.cA * angleC m ^ 2 * differenceL m ^ 2 -
          2 * angleC m * differenceL m * denominatorD m - angleS m ^ 2 * denominatorD m) +
          denominatorK m ^ 2) / denominatorK m ^ 2 := by
  rw [starState, pur, pur, nsq, starPopulation]
  have hK' := hK.ne'
  have hKdef : denominatorK m = denominatorD m - 4 * Complex.normSq m.cA * angleC m * differenceL m := rfl
  generalize denominatorK m = K at *
  rw [eq_div_iff (pow_ne_zero 2 hK')]
  field_simp
  rw [hKdef]
  ring

theorem main (m : Model) (hK : 0 < denominatorK m) :
    purity (starState m) ≤ purity (rho m.pA m.cA) ∧
    (purity (starState m) = purity (rho m.pA m.cA) ↔ m.cA = 0) := by
  have hk := key m hK
  obtain ⟨hp0, hp1, hq⟩ := m.ancilla_physical
  have hq0 : 0 ≤ Complex.normSq m.cA := Complex.normSq_nonneg _
  have hB : 0 < Complex.normSq m.cA →
      0 < (2 * m.pA - 1) ^ 2 * (4 * Complex.normSq m.cA * angleC m ^ 2 * differenceL m ^ 2 -
          2 * angleC m * differenceL m * denominatorD m - angleS m ^ 2 * denominatorD m) +
          denominatorK m ^ 2 := fun hqp =>
    Bpos _ _ _ _ _ (Real.sin (m.frequency * m.duration)) (Real.cos (m.frequency * m.duration)) hqp
      (by nlinarith) (Real.cos_sq_add_sin_sq _) (Real.cos_sq_add_sin_sq _) rfl hK
  have hK2 : 0 < denominatorK m ^ 2 := by positivity
  rcases hq0.lt_or_eq with hqp | hq00
  · have h := hB hqp
    have : 0 < purity (rho m.pA m.cA) - purity (starState m) := by
      rw [hk]; positivity
    refine ⟨by linarith, fun he => by linarith, fun hc => ?_⟩
    rw [hc, Complex.normSq_zero] at hqp; exact absurd hqp (lt_irrefl _)
  · have hc : m.cA = 0 := Complex.normSq_eq_zero.1 hq00.symm
    have : purity (rho m.pA m.cA) - purity (starState m) = 0 := by
      rw [hk, ← hq00]; simp
    exact ⟨by linarith, fun _ => hc, fun _ => by linarith⟩

end X4P32

theorem solution (m : QAlgorithms.Papers.Independent.Information100.P32.Model)
    (hK : 0 < QAlgorithms.Papers.Independent.Information100.P32.denominatorK m) :
    QAlgorithms.Papers.Independent.Information100.P32.purity
        (QAlgorithms.Papers.Independent.Information100.P32.starState m) ≤
      QAlgorithms.Papers.Independent.Information100.P32.purity
        (QAlgorithms.Papers.Independent.Information100.P32.rho m.pA m.cA) ∧
    (QAlgorithms.Papers.Independent.Information100.P32.purity
        (QAlgorithms.Papers.Independent.Information100.P32.starState m) =
      QAlgorithms.Papers.Independent.Information100.P32.purity
        (QAlgorithms.Papers.Independent.Information100.P32.rho m.pA m.cA) ↔ m.cA = 0) :=
  X4P32.main m hK

#print axioms solution
