-- Prove2me | solution 1 for WeierstrassEllipticZeta.stabilizer_local_algebra_degree_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T17:06:55.312985+00:00
-- url     : https://prove2.me/submissions/a50a6acf-51d9-4952-b10c-c5f7dfe13f90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_differential_prime_localization
import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_prime_ideal_degree_budget
import Definitions.Def_TranscendenceTheory_DifferentialMultiplicity
import Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer
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
        ∃ (W : Set (Fin 3 → ℂ)) (b : ℕ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          b ≤ 2 ∧
          ∃ e : GraphExtensionGroup L.lattice η ⧸ linearTranslationImage L.lattice η W → ℕ,
            (∀ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z)), Nonempty (DifferentialMultiplicityWitness U (e c))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hbudget⟩ := stabilizer_prime_ideal_degree_budget L D S
    hS hS_value hS_ne η hη
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, b, hW, hWQ, hb, e, hprime, hsum⟩ :=
    hbudget m n U hm hn hU X h0 Q hQ hne hhigh
  refine ⟨W, b, hW, hWQ, hb, e, ?_, hsum⟩
  intro c hc
  obtain ⟨w⟩ := hprime c hc
  obtain ⟨d, hd, hjets⟩ := differential_prime_localization w.R w.D w.p
  refine ⟨{
    R := Localization.AtPrime w.p
    p := IsLocalRing.maximalIdeal (Localization.AtPrime w.p)
    D := d
    q := algebraMap w.R (Localization.AtPrime w.p) w.q
    q_mem := ?_
    deriv_not_mem := ?_
    I := w.I.map (algebraMap w.R (Localization.AtPrime w.p))
    jets := (hjets w.I U).mp w.jets
    length_le := w.length_le
  }⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ w.p _).mpr w.q_mem
  · intro h
    rw [hd] at h
    exact w.deriv_not_mem ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ w.p _).mp h)

