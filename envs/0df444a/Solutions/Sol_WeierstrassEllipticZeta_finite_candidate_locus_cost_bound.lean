-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_candidate_locus_cost_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T06:57:30.911231+00:00
-- url     : https://prove2.me/submissions/6f609269-f073-4aee-833e-e65731b4dbd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_finite_anchor_candidate_selection
import Theorems.Thm_WeierstrassEllipticZeta_finite_anchor_locus_cost_bound
import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open WeierstrassEllipticZeta
open scoped Pointwise
open TranscendenceTheory

open scoped Classical



noncomputable section
open scoped Pointwise
namespace WeierstrassEllipticZeta

private lemma anchor_last_block_scaling (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → ℂ) (r : ℂ) :
    MvPolynomial.eval ![x 0, x 1, r * x 2, r * x 3, r * x 4, r * x 5, r * x 6] Q =
      r ^ n * MvPolynomial.eval x Q := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

theorem anchor_origin_zero_of_high_order
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (n U : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hS : ∃ j : Fin 5, S j 0 ≠ 0) (X : Finset ℂ) (h0 : 0 ∈ X)
    (hhigh : ∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
      ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z / S j z, S 1 z / S j z,
            S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) :
    MvPolynomial.eval ![1, 0, S 0 0, S 1 0, S 2 0, S 3 0, S 4 0] Q = 0 := by
  classical
  obtain ⟨j, hj⟩ := hS
  have h000 : (0 : ℂ) ∈ X + X + X := by
    simpa using Finset.add_mem_add (Finset.add_mem_add h0 h0) h0
  have hh := hhigh 0 h000 j hj
  have hpos : (0 : ℕ∞) < ((3 * U + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.zero_lt_succ (3 * U)
  have hz : MvPolynomial.eval
      ![1, (0 : ℂ), S 0 0 / S j 0, S 1 0 / S j 0,
        S 2 0 / S j 0, S 3 0 / S j 0, S 4 0 / S j 0] Q = 0 := by
    by_contra hne
    have ho : analyticOrderAt (fun z : ℂ => MvPolynomial.eval
        ![1, z, S 0 z / S j z, S 1 z / S j z,
          S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne)
    exact (not_le_of_gt hpos) (ho ▸ hh)
  have hscale := anchor_last_block_scaling Q n hQ
    ![1, 0, S 0 0, S 1 0, S 2 0, S 3 0, S 4 0] (S j 0)⁻¹
  have heq : (S j 0)⁻¹ ^ n *
      MvPolynomial.eval ![1, 0, S 0 0, S 1 0, S 2 0, S 3 0, S 4 0] Q = 0 := by
    rw [← hscale]
    simpa [div_eq_mul_inv, mul_comm] using hz
  exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero n (inv_ne_zero hj))

end WeierstrassEllipticZeta

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
        ∃ (k : FiniteLocusCandidate L.lattice X) (r : Fin 3 → ℂ),
          (∀ w ∈ candidateLocusSamples L.lattice η X k r m n,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
            S (extensionChartDenominator c) z ≠ 0 ∧
            (((X.image (elementaryPeriodKernel L.lattice η
              (candidateLocusShape L.lattice η X k)).mkQ).card *
              cappedChartCost L S Q (B (m + 2 * n)) U c z : ℕ) : ℝ) ≤
              C * (((elementaryDegree (candidateLocusShape L.lattice η X k) m + 1) *
                n ^ 2 : ℕ) : ℝ) := by
  classical
  obtain ⟨C, hC, hcert⟩ := finite_anchor_locus_cost_bound L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨b, a, c, z, hz, hc, hbudget⟩ :=
    hcert m n U hm hn hU X h0 Q hQ hne hhigh
  have hzero := anchor_origin_zero_of_high_order S Q n U
    (fun d hd => (hQ d hd).2) (hS_ne 0) X h0 hhigh
  have hvalid := ((finite_anchor_candidate_selection L.lattice η X
    S Q m n hQ hzero).1 b).2 a
  exact ⟨anchorCandidateLocus L.lattice η X S Q m n b a,
    anchorCandidatePoint L.lattice η X S Q m n b a,
    hvalid, c, z, hz, hc, hbudget⟩

