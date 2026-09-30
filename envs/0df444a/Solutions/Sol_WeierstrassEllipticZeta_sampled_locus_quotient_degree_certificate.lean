-- Prove2me | solution 1 for WeierstrassEllipticZeta.sampled_locus_quotient_degree_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T05:58:42.062918+00:00
-- url     : https://prove2.me/submissions/d92b0d68-aecd-400d-9482-5510ce9664aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_pure_power_length_profile_realization
import Theorems.Thm_WeierstrassEllipticZeta_sampled_locus_canonical_equation_bound
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
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
            ∃ (o : MonomialOrder.{0, 0} (Fin 4))
              (d : Fin 4 → ℕ) (b : Fin 4 → MvPolynomial (Fin 4) ℂ),
              (∀ i, IsUnit (o.leadingCoeff (b i))) ∧
              (∀ i, o.degree (b i) = Finsupp.single i (d i)) ∧
              ∃ p : (X.image (elementaryPeriodKernel L.lattice η shape).mkQ) →
                PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b)),
                Function.Injective p ∧
                (∀ i, cappedChartCost L S Q (B (m + 2 * n)) U c z ≤
                  (Module.length (Localization.AtPrime (p i).asIdeal)
                    (Localization.AtPrime (p i).asIdeal)).toNat) ∧
                ((Module.finrank ℂ
                  (MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range b)) : ℕ) : ℝ) ≤
                  C * (((elementaryDegree shape m + 1) * n ^ 2 : ℕ) : ℝ) := by
  classical
  obtain ⟨C, hC, hcert⟩ := sampled_locus_canonical_equation_bound L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨shape, r, hsamples, c, z, hz, hc, hbudget⟩ :=
    hcert m n U hm hn hU X h0 Q hQ hne hhigh
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
  let o : MonomialOrder.{0, 0} (Fin 4) := MonomialOrder.degLex
  obtain ⟨hu, hd, _, _, p, hp, he⟩ :=
    pure_power_length_profile_realization ι a ha (fun _ => e) (fun _ => hepos) o
  refine ⟨shape, r, hsamples, c, z, hz, hc, o,
    ![∑ _ : ι, e, 1, 1, 1], b', hu, hd, p, hp, ?_, hbudget⟩
  intro i
  exact le_of_eq (he i).2.symm

