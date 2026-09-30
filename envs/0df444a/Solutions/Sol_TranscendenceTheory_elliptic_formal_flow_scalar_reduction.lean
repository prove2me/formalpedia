-- Prove2me | solution 1 for TranscendenceTheory.elliptic_formal_flow_scalar_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T19:19:55.925005+00:00
-- url     : https://prove2.me/submissions/857f5db0-c0a9-4dd9-8dcc-502e34992932

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open scoped Classical

private lemma formal_negative_primitive
    {K : Type*} [Field K] [CharZero K] (a : K) (P : PowerSeries K) :
    let Z := PowerSeries.mk fun n =>
      if n = 0 then a else -PowerSeries.coeff (n - 1) P / (n : K)
    PowerSeries.derivative K Z = -P ∧ PowerSeries.coeff 0 Z = a := by
  constructor
  · ext n
    have hn : (n + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa [PowerSeries.coeff_derivative, Nat.cast_add, Nat.cast_one] using
      div_mul_cancel₀ (-PowerSeries.coeff n P) hn
  · simp

private lemma formal_elliptic_energy
    {K : Type*} [Field K] [CharZero K] (g x y : K) (P : PowerSeries K)
    (h0 : PowerSeries.coeff 0 P = x) (h1 : PowerSeries.coeff 1 P = y)
    (hP : PowerSeries.derivative K (PowerSeries.derivative K P) =
      PowerSeries.C 6 * P ^ 2 - PowerSeries.C (g / 2)) :
    (PowerSeries.derivative K P) ^ 2 - PowerSeries.C 4 * P ^ 3 +
      PowerSeries.C g * P = PowerSeries.C (y ^ 2 - 4 * x ^ 3 + g * x) := by
  have hhalf : (2 : PowerSeries K) * PowerSeries.C (g / 2) = PowerSeries.C g := by
    calc
      _ = PowerSeries.C ((2 : K) * (g / 2)) := by rw [map_mul, map_ofNat]
      _ = _ := by congr 1; field_simp
  apply PowerSeries.derivative.ext
  · simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_pow, PowerSeries.derivative_C, hP,
      Nat.reduceSub, mul_zero, add_zero, map_ofNat]
    have hd4 : PowerSeries.derivative K (4 : PowerSeries K) = 0 := by
      simpa only [Nat.cast_ofNat] using! (PowerSeries.derivative K).map_natCast 4
    rw [hd4]
    linear_combination -(PowerSeries.derivative K P) * hhalf
  · have hc0 : PowerSeries.constantCoeff P = x := by simpa using h0
    have hc1 : PowerSeries.constantCoeff (PowerSeries.derivative K P) = y := by
      simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_derivative] using h1
    simp [hc0, hc1]

theorem solution
    (K : Type*) [Field K] [CharZero K] (g : K) (v : Fin 4 → K)
    (J : Fin 4 → PowerSeries K) :
    let R : PowerSeries K → Fin 4 → PowerSeries K := fun P =>
      ![PowerSeries.C (v 0) + PowerSeries.X, P, PowerSeries.derivative K P,
        PowerSeries.mk fun n =>
          if n = 0 then v 3 else -PowerSeries.coeff (n - 1) P / (n : K)]
    ((∀ a, PowerSeries.coeff 0 (J a) = v a) ∧
      PowerSeries.derivative K (J 0) = 1 ∧
      PowerSeries.derivative K (J 1) = J 2 ∧
      PowerSeries.derivative K (J 2) =
        PowerSeries.C 6 * (J 1) ^ 2 - PowerSeries.C (g / 2) ∧
      PowerSeries.derivative K (J 3) = -J 1) ↔
    ∃ P : PowerSeries K,
      PowerSeries.coeff 0 P = v 1 ∧ PowerSeries.coeff 1 P = v 2 ∧
      PowerSeries.derivative K (PowerSeries.derivative K P) =
        PowerSeries.C 6 * P ^ 2 - PowerSeries.C (g / 2) ∧
      (PowerSeries.derivative K P) ^ 2 - PowerSeries.C 4 * P ^ 3 +
        PowerSeries.C g * P =
          PowerSeries.C ((v 2) ^ 2 - 4 * (v 1) ^ 3 + g * v 1) ∧
      J = R P := by
  classical
  dsimp only
  constructor
  · rintro ⟨hinit, h0, h1, h2, h3⟩
    have hc1 : PowerSeries.coeff 1 (J 1) = v 2 := by
      have h := congrArg (PowerSeries.coeff 0) h1
      simpa [PowerSeries.coeff_derivative, hinit] using h
    have hsecond : PowerSeries.derivative K (PowerSeries.derivative K (J 1)) =
        PowerSeries.C 6 * (J 1) ^ 2 - PowerSeries.C (g / 2) := by rw [h1, h2]
    refine ⟨J 1, hinit 1, hc1, hsecond,
      formal_elliptic_energy g (v 1) (v 2) (J 1) (hinit 1) hc1 hsecond, ?_⟩
    funext a
    fin_cases a
    · apply PowerSeries.derivative.ext
      · simpa using h0
      · simpa using hinit 0
    · rfl
    · exact h1.symm
    · apply PowerSeries.derivative.ext
      · exact h3.trans (formal_negative_primitive (v 3) (J 1)).1.symm
      · simpa using hinit 3
  · rintro ⟨P, h0, h1, hsecond, _henergy, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a
      fin_cases a
      · simp
      · exact h0
      · simpa [PowerSeries.coeff_derivative] using h1
      · simp
    · simp
    · rfl
    · exact hsecond
    · exact (formal_negative_primitive (v 3) P).1
