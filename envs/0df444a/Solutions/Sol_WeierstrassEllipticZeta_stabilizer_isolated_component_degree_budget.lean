-- Prove2me | solution 1 for WeierstrassEllipticZeta.stabilizer_isolated_component_degree_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T18:45:52.960339+00:00
-- url     : https://prove2.me/submissions/5c6cd780-b0fb-434b-98ed-7d87defb473e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_TranscendenceTheory_minimal_prime_primary_component
import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_minimal_prime_degree_budget
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
              (extensionCurve L.lattice η z)), Nonempty (IsolatedComponentMultiplicityData U (e c))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hbudget⟩ := stabilizer_minimal_prime_degree_budget L D S
    hS hS_value hS_ne η hη
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, b, hW, hWQ, hb, e, hcomponents, hsum⟩ :=
    hbudget m n U hm hn hU X h0 Q hQ hne hhigh
  refine ⟨W, b, hW, hWQ, hb, e, ?_, hsum⟩
  intro c hc
  obtain ⟨w⟩ := hcomponents c hc
  obtain ⟨J, hcanonical, hIJ, hprimary, hrad, hmap, ⟨K, hK, hsplit⟩,
    hseparator, hfinite, hjets⟩ :=
    minimal_prime_primary_component w.R w.D w.I w.p w.minimal
  have hinter : (⨅ j : Fin 2, ![J, K] j) = w.I := by
    rw [hsplit]
    apply le_antisymm
    · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
    · apply le_iInf
      intro j
      fin_cases j
      · exact inf_le_left
      · exact inf_le_right
  refine ⟨{
    R := w.R
    p := w.p
    D := w.D
    q := w.q
    q_mem := w.q_mem
    deriv_not_mem := w.deriv_not_mem
    n := 2
    J := ![J, K]
    i := 0
    isolated := ?_
    jets := ?_
    length_le := ?_
  }⟩
  · intro j hj
    have heq : j = 1 := by omega
    simpa [heq] using hK
  · rw [hinter]
    exact w.jets
  · rw [hinter]
    exact w.length_le

