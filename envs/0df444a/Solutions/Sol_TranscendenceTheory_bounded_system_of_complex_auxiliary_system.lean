-- Prove2me | solution 1 for TranscendenceTheory.bounded_system_of_complex_auxiliary_system
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T09:53:27.312536+00:00
-- url     : https://prove2.me/submissions/d6809206-a29b-46ca-8ffc-f7379b9a527b

import Definitions.Def_TranscendenceTheory_BoundedBivariateSystem
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Polynomial Finset
open scoped Polynomial

namespace TranscendenceTheory

lemma norm_pow_le_exp (z : ℂ) (k D : ℕ) (hk : k ≤ D) :
    ‖z ^ k‖ ≤ Real.exp (‖z‖ * D) := by
  rw [norm_pow]
  calc
    _ ≤ (Real.exp ‖z‖) ^ k := pow_le_pow_left₀ (norm_nonneg _)
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)) _
    _ = Real.exp (‖z‖ * k) := (Real.exp_nat_mul _ _).symm.trans (by congr 1; ring)
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (norm_nonneg _))

lemma norm_integer_polynomial_eval_le (p : ℤ[X]) (θ : ℂ) (D : ℕ) (H : ℝ)
    (hH : 0 ≤ H) (hD : p.natDegree ≤ D) (hcoeff : ∀ k, ‖p.coeff k‖ ≤ H) :
    ‖aeval θ p‖ ≤ (D + 1 : ℝ) * H * Real.exp (‖θ‖ * D) := by
  change ‖p.eval₂ (algebraMap ℤ ℂ) θ‖ ≤ _
  rw [eval₂_eq_sum_range' _ (hD.trans_lt (Nat.lt_succ_self _))]
  calc
    _ ≤ ∑ k ∈ range (D + 1), ‖(algebraMap ℤ ℂ) (p.coeff k) * θ ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (D + 1), H * Real.exp (‖θ‖ * D) := by
      apply sum_le_sum
      intro k hk
      rw [norm_mul]
      apply mul_le_mul _ (norm_pow_le_exp θ k D (Nat.le_of_lt_succ (mem_range.mp hk)))
        (norm_nonneg _) hH
      change ‖(p.coeff k : ℂ)‖ ≤ H
      simpa only [Complex.norm_intCast, Int.norm_eq_abs] using hcoeff k
    _ = _ := by simp; ring

lemma norm_bivariate_eval_le (p : ℤ[X][X]) (θ ν : ℂ) (D E : ℕ) (H : ℝ)
    (hH : 0 ≤ H) (hE : p.natDegree ≤ E)
    (hD : ∀ j, (p.coeff j).natDegree ≤ D) (hcoeff : ∀ j k, ‖(p.coeff j).coeff k‖ ≤ H) :
    ‖p.eval₂ (aeval θ).toRingHom ν‖ ≤
      (E + 1 : ℝ) * (D + 1) * H * Real.exp (‖θ‖ * D + ‖ν‖ * E) := by
  rw [eval₂_eq_sum_range' _ (hE.trans_lt (Nat.lt_succ_self _))]
  calc
    _ ≤ ∑ j ∈ range (E + 1), ‖aeval θ (p.coeff j) * ν ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (E + 1),
        ((D + 1 : ℝ) * H * Real.exp (‖θ‖ * D)) * Real.exp (‖ν‖ * E) := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (norm_integer_polynomial_eval_le _ θ D H hH (hD j) (hcoeff j))
        (norm_pow_le_exp ν j E (Nat.le_of_lt_succ (mem_range.mp hj)))
        (norm_nonneg _) (by positivity)
    _ = _ := by simp [Real.exp_add]; ring

end TranscendenceTheory

open Polynomial Finset
open scoped Polynomial

open TranscendenceTheory

theorem solution (θ ν : ℂ) (g : ℤ[X][X])
    (hker : ∀ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = 0 → g ∣ p)
    (a c : ℝ) (N : ℕ)
    (S : ComplexAuxiliarySystem θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N)
    (hred : S.yDegree < g.natDegree) :
    Nonempty (BoundedBivariateSystem θ ν a c N) := by
  classical
  refine ⟨{
    rows := S.rows
    cols := S.cols
    tests := S.tests
    xDegree := S.xDegree
    yDegree := S.yDegree
    cols_pos := S.cols_pos
    dimension_gap := S.dimension_gap
    xDegree_le := S.xDegree_le
    yDegree_le := S.yDegree_le
    size_le := S.size_le
    equations := S.equations
    testForms := S.testForms
    equations_yDegree := S.equations_yDegree
    equations_xDegree := S.equations_xDegree
    equations_height := S.equations_height
    testForms_yDegree := S.testForms_yDegree
    testForms_xDegree := S.testForms_xDegree
    testForms_height := S.testForms_height
    small_nonzero := ?_ }⟩
  intro p hp hy hx hcoeff heq
  let ev : ℤ[X][X] →+* ℂ := eval₂RingHom (aeval θ).toRingHom ν
  let z : Fin S.cols → ℂ := fun i => ev (p i)
  have hz : z ≠ 0 := by
    intro hz0
    apply hp
    funext i
    by_contra hi
    have hz_i : (p i).eval₂ (aeval θ).toRingHom ν = 0 := congrFun hz0 i
    have hle := natDegree_le_of_dvd (hker (p i) hz_i) hi
    exact ((hy i).trans_lt hred).not_ge hle
  have hsize : (S.yDegree + 1 : ℝ) * (S.xDegree + 1) ≤ Real.exp (a * N) := by
    have hn : (1 : ℝ) ≤ S.cols := by exact_mod_cast S.cols_pos
    have hmul := mul_le_mul_of_nonneg_right hn
      (show 0 ≤ (S.yDegree + 1 : ℝ) * (S.xDegree + 1) by positivity)
    calc
      _ ≤ (S.cols : ℝ) * (S.yDegree + 1) * (S.xDegree + 1) := by nlinarith only [hmul]
      _ ≤ _ := S.size_le
  have hzbound (i : Fin S.cols) : ‖z i‖ ≤ Real.exp (((3 + ‖θ‖ + ‖ν‖) * a) * N) := by
    change ‖(p i).eval₂ (aeval θ).toRingHom ν‖ ≤ _
    calc
      _ ≤ (S.yDegree + 1 : ℝ) * (S.xDegree + 1) * Real.exp (2 * a * N) *
          Real.exp (‖θ‖ * S.xDegree + ‖ν‖ * S.yDegree) :=
        norm_bivariate_eval_le _ θ ν _ _ _ (Real.exp_pos _).le (hy i) (hx i) (hcoeff i)
      _ ≤ Real.exp (a * N) * Real.exp (2 * a * N) *
          Real.exp (‖θ‖ * S.xDegree + ‖ν‖ * S.yDegree) := by
        gcongr
      _ = Real.exp (a * N + 2 * a * N + ‖θ‖ * S.xDegree + ‖ν‖ * S.yDegree) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hDx := mul_le_mul_of_nonneg_left S.xDegree_le (norm_nonneg θ)
        have hEy := mul_le_mul_of_nonneg_left S.yDegree_le (norm_nonneg ν)
        nlinarith only [hDx, hEy]
  have hzeq (r : Fin S.rows) :
      ∑ i, (S.equations r i).eval₂ (aeval θ).toRingHom ν * z i = 0 := by
    have h := congrArg ev (heq r)
    simpa only [map_sum, map_mul, map_zero, z, ev, coe_eval₂RingHom] using h
  obtain ⟨r, hr0, hrsmall⟩ := S.small_nonzero z hz hzbound hzeq
  refine ⟨r, ?_, ?_⟩
  · change ev (∑ i, S.testForms r i * p i) ≠ 0
    simpa only [map_sum, map_mul, z, ev, coe_eval₂RingHom] using hr0
  · change ‖ev (∑ i, S.testForms r i * p i)‖ ≤ _
    simpa only [map_sum, map_mul, z, ev, coe_eval₂RingHom] using hrsmall

