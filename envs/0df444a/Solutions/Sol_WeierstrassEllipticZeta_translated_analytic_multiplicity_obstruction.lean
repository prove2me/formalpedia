-- Prove2me | solution 1 for WeierstrassEllipticZeta.translated_analytic_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T06:09:47.580982+00:00
-- url     : https://prove2.me/submissions/ff6add73-9155-4294-a9d1-7a5468fd3aae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_projective_locus_stabilizer_construction
import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_locus_multiplicity_bound
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
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

open scoped Classical

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
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
        ∃ (V : Submodule ℂ (Fin 3 → ℂ))
          (H : Submodule ℤ (GraphExtensionGroup L.lattice η))
          (r : Fin 3 → ℂ) (b : ℕ),
          (∀ g, g ∈ H ↔ ∃ v ∈ V,
            g = (v 0, (extensionPeriodGraph L.lattice η).mkQ (v 1, v 2))) ∧
          (∀ v ∈ V,
            MvPolynomial.eval ![1, r 0 + v 0, S 0 (r 1 + v 1), S 1 (r 1 + v 1),
              S 2 (r 1 + v 1), S 3 (r 1 + v 1) + (r 2 + v 2) * S 0 (r 1 + v 1),
              S 4 (r 1 + v 1) + (r 2 + v 2) * S 2 (r 1 + v 1)] Q = 0) ∧ b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) *
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard ≤
            C * (if (∀ v ∈ V, v 0 = 0) then (m : ℝ) else 1) * (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hmult⟩ := stabilizer_locus_multiplicity_bound L D S
    hS hS_value hS_ne η hη
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, b, hW, hWQ, hb, hbound⟩ :=
    hmult m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨hH, _, r, _, hvanish, _, _, _, _⟩ := projective_locus_stabilizer_construction
    L D S hS hS_value hS_ne η Q n (fun d hd => (hQ d hd).2) hne W hW hWQ
  exact ⟨linearTranslationDirections W, linearTranslationImage L.lattice η W,
    r, b, hH, hvanish, hb, hbound⟩

