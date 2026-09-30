-- Prove2me | solution 1 for WeierstrassEllipticZeta.stabilizer_truncated_quotient_rank_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T07:20:13.541397+00:00
-- url     : https://prove2.me/submissions/5456b8a6-222d-4c12-be5b-099d344c0c73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_WeierstrassEllipticZeta_finite_jet_section_interpolation
import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_section_evaluation_rank_budget
import Theorems.Thm_TranscendenceTheory_finite_quotient_degree_stabilization
import Definitions.Def_WeierstrassEllipticZeta_FiniteJetChartIdeals

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


noncomputable section
namespace WeierstrassEllipticZeta
open TranscendenceTheory

/-- The power sandwich forces the quotient dimension to be positive, hence finite. -/
theorem FiniteJetChartIdealData.quotient_finite {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) (i : ι) :
    Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) := by
  apply Module.finite_of_finrank_pos
  by_contra h
  have he : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) = 0 :=
    Nat.eq_zero_of_not_pos h
  have hpow := J.power_le i
  rw [he, pow_zero, Ideal.one_eq_top] at hpow
  exact (inferInstance : (MvPolynomial.vanishingIdeal ℂ {J.point i}).IsMaximal).ne_top
    (top_le_iff.mp (hpow.trans (J.le_point i)))

/-- A punctual finite-jet quotient has a rank certificate at dimension minus one. -/
theorem FiniteJetChartIdealData.degree_rank_certificate {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) (i : ι) :
    let d := Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i)
    Module.finrank ℂ (quotientDegreeImage (J.ideal i) (d - 1)) =
      Module.finrank ℂ (quotientDegreeImage (J.ideal i) (d - 1 + 1)) ∧
    Module.finrank ℂ (quotientDegreeImage (J.ideal i) (d - 1)) = d := by
  dsimp only
  have ht := ((finite_quotient_degree_stabilization ℂ (Fin 4) (J.ideal i)).2
    (J.quotient_finite i)).1
  have ht' : quotientDegreeImage (J.ideal i)
      (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) - 1 + 1) = ⊤ := by
    apply top_unique
    rw [← ht]
    apply Submodule.map_mono
    intro p hp
    exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (Nat.le_succ_of_le ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp))
  rw [ht, ht', finrank_top]
  exact ⟨rfl, rfl⟩

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
        ∃ W : Set (Fin 3 → ℂ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ J : FiniteJetChartIdealData L
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (J.localLength c) (X + X + X))) ∧
            ∃ N : (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z))) → ℕ,
              (∀ c, Module.finrank ℂ (quotientDegreeImage (J.ideal c) (N c)) =
                Module.finrank ℂ (quotientDegreeImage (J.ideal c) (N c + 1))) ∧
              ((∑ c, Module.finrank ℂ (quotientDegreeImage (J.ideal c) (N c)) : ℕ) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by
  classical
  obtain ⟨C, hC, hrank⟩ := stabilizer_section_evaluation_rank_budget L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, hW, hWQ, J, hcomponents, hdim⟩ :=
    hrank m n U hm hn hU X h0 Q hQ hne hhigh
  refine ⟨W, hW, hWQ, J, hcomponents,
    (fun c => Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal c) - 1), ?_, ?_⟩
  · intro c
    exact (J.degree_rank_certificate c).1
  · have he := (finite_jet_section_interpolation L _ J
        (J.totalDimension - 1) (J.totalDimension - 1) le_rfl le_rfl).2.1
    rw [he] at hdim
    simpa only [(J.degree_rank_certificate _).2, FiniteJetChartIdealData.totalDimension] using hdim

