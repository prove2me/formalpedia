-- Prove2me | solution 3 for WeierstrassEllipticZeta.senthil_kumar_theorem_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T01:36:30.340608+00:00
-- url     : https://prove2.me/submissions/d7ea0301-18b8-41d4-b7cd-4effe35459b0

import Theorems.Thm_WeierstrassEllipticZeta_exists_transcendental_parameter_of_no_pair
import Theorems.Thm_TranscendenceTheory_gelfond_polynomial_sequence_lower_bound
import Theorems.Thm_WeierstrassEllipticZeta_small_polynomials_of_algebraic_values
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Filter
open scoped Topology Polynomial

noncomputable section

open WeierstrassEllipticZeta

private theorem linear_small_polynomials_impossible
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (A : ℝ) (hA : 0 < A) (N₀ : ℕ)
    (hsmall : ∀ N : ℕ, N₀ ≤ N → ∃ p : ℤ[X],
      (p.natDegree : ℝ) ≤ A * N ∧
      (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
      0 < ‖Polynomial.aeval θ p‖ ∧
      ‖Polynomial.aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2)) : False := by
  classical
  choose P hP using (fun n : ℕ => hsmall (n + (N₀ + 1)) (by omega))
  let d : ℕ → ℝ := fun n => A * (n + (N₀ + 1) : ℕ)
  have hd_pos : ∀ n, 0 < d n := by
    intro n
    dsimp [d]
    positivity
  have hd_strict : StrictMono d := by
    intro i j hij
    dsimp [d]
    apply mul_lt_mul_of_pos_left _ hA
    exact_mod_cast Nat.add_lt_add_right hij (N₀ + 1)
  have hd_unbounded : Tendsto d atTop atTop := by
    exact Tendsto.const_mul_atTop hA
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N₀ + 1)))
  have hd_growth : ∀ n, d (n + 1) ≤ 2 * d n := by
    intro n
    dsimp [d]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hN : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    nlinarith
  have h_nonzero : ∀ n, Polynomial.aeval θ (P n) ≠ 0 := by
    intro n
    exact norm_pos_iff.mp (hP n).2.2.1
  have h_lower := TranscendenceTheory.gelfond_polynomial_sequence_lower_bound
    θ hθ 2 (by norm_num) d d hd_pos hd_pos hd_strict hd_strict
    hd_unbounded hd_unbounded hd_growth hd_growth P h_nonzero
    (fun n => (hP n).1) (fun n => (hP n).2.1)
  obtain ⟨n, hn⟩ := h_lower.exists
  have h_upper : Real.log ‖Polynomial.aeval θ (P n)‖ ≤ -10 * (d n) ^ 2 := by
    have hlog := Real.log_le_log (hP n).2.2.1 (hP n).2.2.2
    simpa only [Real.log_exp] using hlog
  have hcompare : -(2 * (2 : ℝ) + 1) * d n * (d n + d n) = -10 * (d n) ^ 2 := by
    ring
  rw [hcompare] at hn
  exact (not_lt_of_ge h_upper) hn

/-- The remaining arithmetic reduction uses the proved zeta and elliptic addition
identities. Its two open inputs are the auxiliary polynomial construction and
Gel'fond's polynomial-sequence criterion. -/
theorem solution (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0)
    (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥) :
    HasAlgebraicallyIndependentPair (theoremOneValues L ω u₁ u₂) := by
  classical
  by_contra hpair
  obtain ⟨θ, hθ, h_values⟩ :=
    exists_transcendental_parameter_of_no_pair (theoremOneValues L ω u₁ u₂) hpair
  obtain ⟨A, hA, N₀, hsmall⟩ := small_polynomials_of_algebraic_values
    L ω u₁ u₂ hω_ne hω_period h_linearIndependent h_intersection
    (hasDerivAt_weierstrassZeta L) (zeta_addition_formula L) (wp_addition_formula L)
    θ hθ h_values
  exact linear_small_polynomials_impossible θ hθ A hA N₀ hsmall

