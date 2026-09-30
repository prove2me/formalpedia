-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_set_projective_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T16:16:53.897573+00:00
-- url     : https://prove2.me/submissions/76de5f4b-81e1-4922-a70a-cf1c37fad94f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_quotient_group_projective_multiplicity_obstruction
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) →
        ∃ K : Submodule ℤ ℂ, ∃ a b : ℕ,
          ((a = 1 ∧ K = ⊥) ∨ (a = 0 ∧ K ≤ L.lattice)) ∧ b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by
  obtain ⟨η, hη, hgeometry⟩ := elliptic_extension_group_geometry L
  obtain ⟨C, hC, hobstruction⟩ :=
    quotient_group_projective_multiplicity_obstruction L D S hS hS_value hS_ne η hη
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hF hhigh
  obtain ⟨H, a, b, hprofile, hb, hupper⟩ :=
    hobstruction m n U hm hn hU X h0 Q hQ hF hhigh
  have hpull := hgeometry.2.2.2.2.2 H
  refine ⟨H.comap (extensionCurve L.lattice η), a, b, ?_, hb, ?_⟩
  · rcases hprofile with ⟨ha, hH⟩ | ⟨ha, hH⟩
    · exact Or.inl ⟨ha, hpull.1 hH⟩
    · exact Or.inr ⟨ha, hpull.2.1 hH⟩
  · rw [hpull.2.2 X]
    exact hupper
