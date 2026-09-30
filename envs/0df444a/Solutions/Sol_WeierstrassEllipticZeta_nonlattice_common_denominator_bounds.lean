-- Prove2me | solution 1 for WeierstrassEllipticZeta.nonlattice_common_denominator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T00:39:49.355844+00:00
-- url     : https://prove2.me/submissions/a9d7ddbd-ecb0-4119-b54b-82cc333892cd

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 800000

open Filter
open scoped BigOperators

open WeierstrassEllipticZeta

private lemma norm_mv_eval_le (p : MvPolynomial (Fin 2) ℤ) (θ ν : ℂ)
    (d : ℕ) (t H : ℝ) (ht : 1 ≤ t) (hθ : ‖θ‖ ≤ t) (hν : ‖ν‖ ≤ t)
    (hd : p.totalDegree ≤ d)
    (hH : ((∑ b ∈ p.support, (p.coeff b).natAbs) : ℝ) ≤ H) :
    ‖MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] p‖ ≤ H * t ^ d := by
  classical
  rw [MvPolynomial.eval₂_eq']
  change ‖∑ b ∈ p.support, ((p.coeff b : ℤ) : ℂ) * ∏ i : Fin 2, ![θ, ν] i ^ b i‖ ≤ _
  calc
    _ ≤ ∑ b ∈ p.support, ‖((p.coeff b : ℤ) : ℂ) * ∏ i : Fin 2, ![θ, ν] i ^ b i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b ∈ p.support, ((p.coeff b).natAbs : ℝ) * t ^ d := by
      apply Finset.sum_le_sum
      intro b hb
      have hbd : b 0 + b 1 ≤ d := by
        have h := (MvPolynomial.le_totalDegree hb).trans hd
        simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using h
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_mul, norm_pow, Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        ‖θ‖ ^ b 0 * ‖ν‖ ^ b 1 ≤ t ^ b 0 * t ^ b 1 := by gcongr
        _ = t ^ (b 0 + b 1) := (pow_add _ _ _).symm
        _ ≤ t ^ d := pow_le_pow_right₀ ht hbd
    _ = ((∑ b ∈ p.support, (p.coeff b).natAbs) : ℝ) * t ^ d := by
      simp only [Finset.sum_mul]
    _ ≤ H * t ^ d := mul_le_mul_of_nonneg_right hH (by positivity)

private lemma norm_mv_eval_le_exp (p : MvPolynomial (Fin 2) ℤ) (θ ν : ℂ)
    (d : ℕ) (t h : ℝ) (ht : 1 ≤ t) (hθ : ‖θ‖ ≤ t) (hν : ‖ν‖ ≤ t)
    (hd : p.totalDegree ≤ d)
    (hh : ((∑ b ∈ p.support, (p.coeff b).natAbs) : ℝ) ≤ Real.exp h) :
    ‖MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] p‖ ≤
      Real.exp (h + d * Real.log t) := by
  have h := norm_mv_eval_le p θ ν d t (Real.exp h) ht hθ hν hd hh
  rwa [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith : 0 < t)]

/-- Uniform norm bounds for the common moving denominator and the residual jet factor. -/
theorem solution (θ ν : ℂ) (C : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : PeriodPair) (v z : ℂ) (N s : ℕ),
      1 ≤ Real.log N → ∀ P : NonlatticeCoordinatePresentation L θ ν v z C N s,
        let E : Fin 8 → ℂ := fun a =>
          MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
        let Q := E 1 * E 2 * E 3
        Q ≠ 0 ∧
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) ∧
          ∀ m l n : ℕ,
            ‖E 0 ^ m * (E 4 * E 5 * E 6 * E 7) ^ (m + 5 * l + n)‖ ≤
              Real.exp (B * ((m : ℝ) * Real.log N + m + 5 * l + n)) := by
  let t : ℝ := 1 + ‖θ‖ + ‖ν‖
  have ht : 1 ≤ t := by dsimp [t]; linarith [norm_nonneg θ, norm_nonneg ν]
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  let b : ℝ := C * (1 + Real.log t)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨4 * b + 4, by positivity, ?_⟩
  intro L v z N s hN P
  let E : Fin 8 → ℂ := fun a =>
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
  let U : Fin 8 → ℂ := fun a =>
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.numerator a)
  let T : ℝ := (s : ℝ) ^ 2 + Real.log N
  let V : Fin 8 → ℝ := ![b * Real.log N, b * T, b * T, b * T, b, b, b, b]
  have hT : 1 ≤ T := by dsimp [T]; nlinarith [sq_nonneg (s : ℝ)]
  have hprofile (a : Fin 8) :
      nonlatticeCoordinateLogBound C N s a +
        nonlatticeCoordinateDegree C s a * Real.log t ≤ V a := by
    have h0 := mul_le_mul_of_nonneg_left hN
      (mul_nonneg (Nat.cast_nonneg C) hlog)
    have h1 := mul_nonneg (mul_nonneg (Nat.cast_nonneg C) hlog) (by linarith : 0 ≤ Real.log N)
    fin_cases a <;>
      simp [nonlatticeCoordinateLogBound, nonlatticeCoordinateDegree, V, b, T] <;>
      nlinarith only [h0, h1]
  have hE (a : Fin 8) : ‖E a‖ ≤ Real.exp (V a) := by
    apply (norm_mv_eval_le_exp (P.denominator a) θ ν _ t _ ht
      (by dsimp [t]; linarith [norm_nonneg ν])
      (by dsimp [t]; linarith [norm_nonneg θ]) (P.denominator_degree a) ?_).trans
    · exact Real.exp_le_exp.mpr (hprofile a)
    · refine le_trans ?_ (P.length_le a)
      exact_mod_cast P.denominator_length a
  have hU (a : Fin 8) : ‖U a‖ ≤ Real.exp (V a) := by
    apply (norm_mv_eval_le_exp (P.numerator a) θ ν _ t _ ht
      (by dsimp [t]; linarith [norm_nonneg ν])
      (by dsimp [t]; linarith [norm_nonneg θ]) (P.numerator_degree a) ?_).trans
    · exact Real.exp_le_exp.mpr (hprofile a)
    · refine le_trans ?_ (P.length_le a)
      exact_mod_cast P.numerator_length a
  have hthree (x y w : ℂ) (hx : ‖x‖ ≤ Real.exp (b * T))
      (hy : ‖y‖ ≤ Real.exp (b * T)) (hw : ‖w‖ ≤ Real.exp (b * T)) :
      ‖x * y * w‖ ≤ Real.exp (3 * b * T) := by
    calc
      _ = ‖x‖ * ‖y‖ * ‖w‖ := by simp only [norm_mul]
      _ ≤ Real.exp (b * T) * Real.exp (b * T) * Real.exp (b * T) := by gcongr
      _ = Real.exp (3 * b * T) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he1 : U 1 = E 1 * weierstrassZeta L v := by
    simpa [U, E, ellipticJetCoordinates] using P.evaluation 1
  have he2 : U 2 = E 2 * L.weierstrassP v := by
    simpa [U, E, ellipticJetCoordinates] using P.evaluation 2
  have he3 : U 3 = E 3 * L.derivWeierstrassP v := by
    simpa [U, E, ellipticJetCoordinates] using P.evaluation 3
  have hc0 := hthree (E 1) (E 2) (E 3) (hE 1) (hE 2) (hE 3)
  have hc1 : ‖E 1 * E 2 * E 3 * weierstrassZeta L v‖ ≤ Real.exp (3 * b * T) := by
    calc
      _ = ‖U 1 * E 2 * E 3‖ := by rw [he1]; congr 1; ring
      _ ≤ _ := hthree _ _ _ (hU 1) (hE 2) (hE 3)
  have hc2 : ‖E 1 * E 2 * E 3 * L.weierstrassP v‖ ≤ Real.exp (3 * b * T) := by
    calc
      _ = ‖E 1 * U 2 * E 3‖ := by rw [he2]; congr 1; ring
      _ ≤ _ := hthree _ _ _ (hE 1) (hU 2) (hE 3)
  have hc3 : ‖E 1 * E 2 * E 3 * L.derivWeierstrassP v‖ ≤ Real.exp (3 * b * T) := by
    calc
      _ = ‖E 1 * E 2 * U 3‖ := by rw [he3]; congr 1; ring
      _ ≤ _ := hthree _ _ _ (hE 1) (hE 2) (hU 3)
  refine ⟨mul_ne_zero (mul_ne_zero (P.denominator_ne_zero 1)
    (P.denominator_ne_zero 2)) (P.denominator_ne_zero 3), ?_, ?_⟩
  · calc
      _ ≤ 4 * Real.exp (3 * b * T) := by linarith
      _ ≤ Real.exp 4 * Real.exp (3 * b * T) := by
        gcongr
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = Real.exp (4 + 3 * b * T) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((4 * b + 4) * T) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hb (by linarith : 0 ≤ T)]
  · intro m l n
    have hfixed : ‖E 4 * E 5 * E 6 * E 7‖ ≤ Real.exp (4 * b) := by
      calc
        _ = ‖E 4‖ * ‖E 5‖ * ‖E 6‖ * ‖E 7‖ := by simp only [norm_mul]
        _ ≤ Real.exp b * Real.exp b * Real.exp b * Real.exp b := by
          gcongr
          · exact hE 4
          · exact hE 5
          · exact hE 6
          · exact hE 7
        _ = Real.exp (4 * b) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc
      _ = ‖E 0‖ ^ m * ‖E 4 * E 5 * E 6 * E 7‖ ^ (m + 5 * l + n) := by
        simp only [norm_mul, norm_pow]
        rfl
      _ ≤ Real.exp (b * Real.log N) ^ m * Real.exp (4 * b) ^ (m + 5 * l + n) := by
        gcongr
        exact hE 0
      _ = Real.exp (b * ((m : ℝ) * Real.log N) +
          4 * b * (m + 5 * l + n)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        congr 1
        ring
      _ ≤ Real.exp ((4 * b + 4) * ((m : ℝ) * Real.log N + m + 5 * l + n)) := by
        apply Real.exp_le_exp.mpr
        have hml : 0 ≤ (m : ℝ) * Real.log N := by positivity
        nlinarith [mul_nonneg hb hml,
          mul_nonneg hb (by positivity : (0 : ℝ) ≤ m + 5 * l + n)]
