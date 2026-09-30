-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_set_projective_chart_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T15:36:40.36798+00:00
-- url     : https://prove2.me/submissions/d5077dee-9520-4e3e-8303-d169a86c5ac8

import Theorems.Thm_TranscendenceTheory_finite_set_subgroup_obstruction_exclusion
import Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_multiplicity_obstruction
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n T : ℕ,
      1 ≤ m → 1 ≤ n → 3 ≤ T → ∀ X : Finset ℂ,
      0 ∈ X →
      3 * C * (m : ℝ) * (n : ℝ) ^ 2 < (T : ℝ) * X.card →
      3 * C * (n : ℝ) ^ 2 <
        (T : ℝ) * (L.lattice.mkQ '' (X : Set ℂ)).ncard →
      ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        ∃ v ∈ X + X + X, ∃ j : Fin 5, S j v ≠ 0 ∧
          analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v ≤ T := by
  classical
  obtain ⟨C, hC, hobstruction⟩ :=
    finite_set_projective_multiplicity_obstruction L D S hS hS_value hS_ne
  refine ⟨C, hC, ?_⟩
  intro m n T hm hn hT X h0 hfirst hsecond Q hQ hF
  by_contra hno
  have hU : 1 ≤ T / 3 := by omega
  have hbound : 3 * (T / 3) + 1 ≤ T + 1 := by omega
  have hhigh : ∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
      ((3 * (T / 3) + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z / S j z, S 1 z / S j z,
            S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v := by
    intro v hv j hj
    have hnot : ¬ analyticOrderAt
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z / S j z, S 1 z / S j z,
            S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v ≤ T :=
      fun hle => hno ⟨v, hv, j, hj, hle⟩
    have hsucc := (ENat.add_one_le_iff (by simp)).mpr (lt_of_not_ge hnot)
    have hbound' : ((3 * (T / 3) + 1 : ℕ) : ℕ∞) ≤ (T : ℕ∞) + 1 := by
      exact_mod_cast hbound
    exact hbound'.trans hsucc
  obtain ⟨K, a, b, hprofile, hb, hupper⟩ :=
    hobstruction m n (T / 3) hm hn hU X h0 Q hQ hF hhigh
  have hlower := TranscendenceTheory.finite_set_subgroup_obstruction_exclusion
    ℤ ℂ L.lattice X C hC m n T hm hn hfirst hsecond K a b hprofile hb
  exact (not_lt_of_ge hupper) hlower
