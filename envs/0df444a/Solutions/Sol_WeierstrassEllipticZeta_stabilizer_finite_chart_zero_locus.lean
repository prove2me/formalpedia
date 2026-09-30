-- Prove2me | solution 1 for WeierstrassEllipticZeta.stabilizer_finite_chart_zero_locus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T02:53:53.021271+00:00
-- url     : https://prove2.me/submissions/243b2618-063d-41e7-9137-1b43131daee3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_TranscendenceTheory_finite_punctual_ideal_decomposition
import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_punctual_chart_ideals
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
        ∃ W : Set (Fin 3 → ℂ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          ∃ J : FiniteChartZeroLocusData L
            (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z))),
            (∀ c, Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U
              (J.localLength c) (X + X + X))) ∧
            (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal) : ℝ) ≤
              C * (Module.finrank ℂ (firstChartSectionSpace L
                (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then m else 0) n) : ℝ) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := stabilizer_punctual_chart_ideals L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, hW, hWQ, P, hcomponents, hdim⟩ :=
    hlocal m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨hzero, hfinite, hdimension, hmap⟩ :=
    (finite_punctual_ideal_decomposition ℂ (Fin 4) _ P.point P.point_injective).1
      P.ideal P.zeroLocus_eq
  let J : FiniteChartZeroLocusData L
      (X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
        (extensionCurve L.lattice η z))) :=
    { ideal := ⨅ c, P.ideal c
      cubic_mem := Ideal.mem_iInf.mpr P.cubic_mem
      finite_zeroLocus := hzero ▸ Set.finite_range P.point
      point := P.point
      point_injective := P.point_injective
      point_mem := fun c => hzero ▸ ⟨c, rfl⟩ }
  refine ⟨W, hW, hWQ, J, ?_, ?_⟩
  · intro c
    have he : J.localLength c = P.localLength c := by
      change (Module.length
        (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (P.point c)).asIdeal)
        ((Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (P.point c)).asIdeal) ⧸
          (⨅ j, P.ideal j).map (algebraMap (MvPolynomial (Fin 4) ℂ)
            (Localization.AtPrime (MvPolynomial.pointToPoint (k := ℂ) (P.point c)).asIdeal)))).toNat = _
      rw [hmap c]
      rfl
    rw [he]
    exact hcomponents c
  · change (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ ⨅ c, P.ideal c) : ℝ) ≤ _
    rw [hdimension]
    exact hdim

