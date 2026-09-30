-- Prove2me | solution 1 for WeierstrassEllipticZeta.sampled_locus_canonical_equation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T06:30:15.519181+00:00
-- url     : https://prove2.me/submissions/45a1f67f-426f-4712-9aea-fe474e5be919
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_finite_locus_candidate_selection
import Theorems.Thm_WeierstrassEllipticZeta_finite_candidate_locus_cost_bound
import Theorems.Thm_TranscendenceTheory_pure_power_length_profile_realization
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
import Mathlib.RingTheory.MvPolynomial.Groebner
import Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
import Definitions.Def_WeierstrassEllipticZeta_ElementaryLoci
import Definitions.Def_WeierstrassEllipticZeta_CanonicalChartCost
import Definitions.Def_WeierstrassEllipticZeta_SectionJetEvaluation
import Definitions.Def_TranscendenceTheory_PolynomialQuotientDegreeFiltration
import Definitions.Def_WeierstrassEllipticZeta_FiniteJetChartIdeals
import Definitions.Def_WeierstrassEllipticZeta_PunctualChartIdeals
import Definitions.Def_WeierstrassEllipticZeta_FiniteChartZeroLocus
import Definitions.Def_WeierstrassEllipticZeta_ChartQuotientMultiplicity
import Definitions.Def_TranscendenceTheory_FiniteAlgebraMultiplicityModel
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Definitions.Def_WeierstrassEllipticZeta_CappedChartJets
import Definitions.Def_WeierstrassEllipticZeta_FiniteChartJets
import Definitions.Def_WeierstrassEllipticZeta_CubicChartBase
import Definitions.Def_WeierstrassEllipticZeta_FirstCubicChartBase
import Definitions.Def_WeierstrassEllipticZeta_GlobalChartBase
import Definitions.Def_WeierstrassEllipticZeta_ChartOrbitBase
import Definitions.Def_WeierstrassEllipticZeta_ChartSelectionData
import Definitions.Def_WeierstrassEllipticZeta_ChartProlongationData
import Definitions.Def_WeierstrassEllipticZeta_ChartPrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_AnalyticOrbitMultiplicityData
import Definitions.Def_TranscendenceTheory_MinimalPrimeMultiplicityData
import Definitions.Def_TranscendenceTheory_IsolatedComponentMultiplicityData
import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
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
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (B : ℕ → ℕ)
    (hB : ∀ (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ),
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) →
      ∀ (c : Fin 2) (T : ℕ), extensionChartJetIdeal L Q c T =
        extensionChartJetIdeal L Q c (min T (B (m + 2 * n)))) :
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
        ∃ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
          (∀ w ∈ elementaryLocusSamples shape r m n,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            let ι : Type := (X.image (elementaryPeriodKernel L.lattice η shape).mkQ)
            let e := cappedChartCost L S Q (B (m + 2 * n)) U c z
            let b : Fin 4 → MvPolynomial (Fin 4) ℂ :=
              ![∏ i : ι, (MvPolynomial.X 0 -
                MvPolynomial.C (((Fintype.equivFin ι i).val : ℕ) : ℂ)) ^ e,
                MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3]
            ((Module.finrank ℂ
              (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b)) : ℕ) : ℝ) ≤
              C * (((elementaryDegree shape m + 1) * n ^ 2 : ℕ) : ℝ) := by
  classical
  obtain ⟨C, hC, hcert⟩ := finite_candidate_locus_cost_bound L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨k, r, hsamples, c, z, hz, hc, hbudget⟩ :=
    hcert m n U hm hn hU X h0 Q hQ hne hhigh
  let shape := candidateLocusShape L.lattice η X k
  have hcanonical := ((finite_locus_candidate_selection L.lattice η X
    S Q m n hQ).2.1 k r).mp hsamples
  let ι : Type := (X.image (elementaryPeriodKernel L.lattice η shape).mkQ)
  let a : ι → ℂ := fun i => ((Fintype.equivFin ι i).val : ℂ)
  have ha : Function.Injective a := by
    intro i j hij
    apply (Fintype.equivFin ι).injective
    apply Fin.ext
    exact Nat.cast_injective hij
  let e := cappedChartCost L S Q (B (m + 2 * n)) U c z
  have hepos : 0 < e := Nat.zero_lt_one.trans_le (le_max_left _ _)
  let b' : Fin 4 → MvPolynomial (Fin 4) ℂ :=
    ![∏ i : ι, (MvPolynomial.X 0 - MvPolynomial.C (a i)) ^ e,
      MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3]
  have hdim0 := (pure_power_length_profile_realization ι a ha
    (fun _ => e) (fun _ => hepos) MonomialOrder.degLex).2.2.2.1
  have hdim : Module.finrank ℂ
      (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b')) =
      (X.image (elementaryPeriodKernel L.lattice η shape).mkQ).card * e := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ι, Fintype.card_coe, Nat.cast_id] using hdim0
  refine ⟨shape, r, hcanonical, c, z, hz, hc, ?_⟩
  change ((Module.finrank ℂ
    (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b'))) : ℝ) ≤ _
  rw [hdim]
  exact hbudget

