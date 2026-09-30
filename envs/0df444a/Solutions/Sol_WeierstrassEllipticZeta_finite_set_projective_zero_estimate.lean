-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_set_projective_zero_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T15:07:02.938563+00:00
-- url     : https://prove2.me/submissions/9cae9bd7-ff27-41d2-826b-ad931f95ed91

import Theorems.Thm_TranscendenceTheory_projective_chart_vanishing_order
import Theorems.Thm_WeierstrassEllipticZeta_finite_set_projective_chart_zero_estimate
import Mathlib.Tactic.FinCases
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
        ∃ v ∈ X + X + X, ∃ j : ℕ, j ≤ T ∧ iteratedDeriv j
          (fun z : ℂ => MvPolynomial.eval
            ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) v ≠ 0 := by
  obtain ⟨C, hC, hzero⟩ := finite_set_projective_chart_zero_estimate L D S hS hS_value hS_ne
  refine ⟨C, hC, ?_⟩
  intro m n T hm hn hT X h0 hfirst hsecond Q hQ hH
  obtain ⟨v, hv, j, hj, horder⟩ :=
    hzero m n T hm hn hT X h0 hfirst hsecond Q hQ hH
  have hlocal := TranscendenceTheory.projective_chart_vanishing_order
    ![fun _ : ℂ => 1, fun w : ℂ => w] S Q n (fun d hd => (hQ d hd).2) v j hj
    (by
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_id)
    (fun i => hS i v trivial)
  obtain ⟨k, hk, hne⟩ := (hlocal.2.2.2 T).mp horder
  exact ⟨v, hv, k, hk, hne⟩
