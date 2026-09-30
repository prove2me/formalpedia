-- Prove2me | solution 1 for WeierstrassEllipticZeta.stabilizer_capped_chart_jet_degree_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T00:16:05.914832+00:00
-- url     : https://prove2.me/submissions/6bc3a9af-0826-4b81-b27b-56dcb12af2f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_section_dimension
import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_chart_section_dimension_budget
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



namespace WeierstrassEllipticZeta

theorem section_dimension_profile_bound (L : PeriodPair) (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (P : Prop) [Decidable P] :
    (Module.finrank ℂ (firstChartSectionSpace L (if P then m else 0) n) : ℝ) ≤
      60 * (if P then (m : ℝ) else 1) * (n : ℝ) ^ 2 := by
  by_cases hP : P
  · have hindex := congrArg (fun a : ℕ =>
      (Module.finrank ℂ (firstChartSectionSpace L a n) : ℝ)) (if_pos hP : (if P then m else 0) = m)
    rw [hindex, if_pos hP]
    have hdim := (elliptic_first_chart_section_dimension L m n).2.2 hn
    have hnat : Module.finrank ℂ (firstChartSectionSpace L m n) ≤ 60 * m * n ^ 2 :=
      hdim.trans (Nat.mul_le_mul_right _ (by omega))
    exact_mod_cast hnat
  · have hindex := congrArg (fun a : ℕ =>
      (Module.finrank ℂ (firstChartSectionSpace L a n) : ℝ)) (if_neg hP : (if P then m else 0) = 0)
    rw [hindex, if_neg hP, mul_one]
    have hdim := (elliptic_first_chart_section_dimension L 0 n).2.2 hn
    have hnat : Module.finrank ℂ (firstChartSectionSpace L 0 n) ≤ 60 * n ^ 2 :=
      hdim.trans (Nat.mul_le_mul_right _ (by decide : 30 * (0 + 1) ≤ 60))
    exact_mod_cast hnat

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
        ∃ (W : Set (Fin 3 → ℂ)) (b : ℕ), W.Nonempty ∧
          (∀ w ∈ W,
            MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
              S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q = 0) ∧
          b ≤ 2 ∧
          ∃ e : GraphExtensionGroup L.lattice η ⧸ linearTranslationImage L.lattice η W → ℕ,
            (∀ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
              (extensionCurve L.lattice η z)), Nonempty (CappedChartJetBudget L S Q (B (m + 2 * n)) U (e c) (X + X + X))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hbudget⟩ := stabilizer_chart_section_dimension_budget L D S
    hS hS_value hS_ne η hη B hB
  refine ⟨60 * C, mul_pos (by norm_num) hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, hW, hWQ, e, hcomponents, hsum⟩ :=
    hbudget m n U hm hn hU X h0 Q hQ hne hhigh
  refine ⟨W, 2, hW, hWQ, le_rfl, e, hcomponents, ?_⟩
  have hdim := section_dimension_profile_bound L m n hm hn
    (∀ v ∈ linearTranslationDirections W, v 0 = 0)
  calc
    _ ≤ C * (60 * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0)
        then (m : ℝ) else 1) * (n : ℝ) ^ 2) :=
      hsum.trans (mul_le_mul_of_nonneg_left hdim hC.le)
    _ = _ := by ring

