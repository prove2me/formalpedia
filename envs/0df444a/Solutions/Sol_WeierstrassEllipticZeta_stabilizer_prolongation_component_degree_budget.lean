-- Prove2me | solution 1 for WeierstrassEllipticZeta.stabilizer_prolongation_component_degree_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T20:09:56.063989+00:00
-- url     : https://prove2.me/submissions/727824b9-890b-4878-949c-717bfe5781c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_three_step_minimal_prime_selection
import Definitions.Def_WeierstrassEllipticZeta_ChartSelectionData
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic

import Theorems.Thm_WeierstrassEllipticZeta_stabilizer_height_selection_degree_budget
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
open TranscendenceTheory

/-- Construct the prime and its stage from the explicit height-selection data. -/
theorem chart_selection_to_prolongation
    (L : PeriodPair) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (T e : ℕ)
    (w : ChartSelectionMultiplicityData L S Q T e) :
    Nonempty (ChartProlongationMultiplicityData L S Q T e) := by
  classical
  let δ := extensionChartDerivation L.g₂ L.g₃ w.chart
  let q := RingHom.ker (MvPolynomial.eval (extensionChartCoordinates S w.chart w.z))
  let : q.IsPrime := RingHom.ker_isPrime _
  let J : Fin 4 → Ideal (MvPolynomial (Fin 4) ℂ) :=
    fun i => differentialProlongation δ w.base (i.val * T)
  have hzero : differentialProlongation δ w.base 0 = w.base := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro r ⟨f, hf, k, hk, heq⟩
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa using heq ▸ hf
    · intro f hf
      exact Ideal.subset_span ⟨f, hf, 0, le_refl 0, rfl⟩
  have hmono : Monotone J := by
    intro i j hij
    apply Ideal.span_mono
    rintro r ⟨f, hf, k, hk, heq⟩
    exact ⟨f, hf, k, hk.trans (Nat.mul_le_mul_right T hij), heq⟩
  have hdim : ringKrullDim (MvPolynomial (Fin 4) ℂ) = 4 := by simp
  have hupper : q.height ≤ (4 : ℕ∞) := by
    have h := q.height_le_ringKrullDim_of_isPrime
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hlower : (2 : ℕ∞) ≤ (J 0).height := by
    simpa only [J, Fin.val_zero, zero_mul, hzero] using w.height_lower
  obtain ⟨i, p, hpq, hstart, hend⟩ := three_step_minimal_prime_selection
    (MvPolynomial (Fin 4) ℂ) J hmono q w.terminal hlower hupper
  have hstart' : p ∈ (differentialProlongation δ w.base (i.val * T)).minimalPrimes :=
    hstart
  have hend' : p ∈ (differentialProlongation δ w.base ((i.val + 1) * T)).minimalPrimes :=
    hend
  let : p.IsPrime := hstart'.isPrime
  refine ⟨{
    chart := w.chart
    z := w.z
    chart_ne := w.chart_ne
    base := w.base
    stage := i.val * T
    p := p
    minimal_start := hstart'
    minimal_end := ?_
    normalized_mem := hstart'.le (Ideal.subset_span
      ⟨_, w.normalized_mem, 0, Nat.zero_le _, rfl⟩)
    point_on_prime := ?_
    length_le := w.length_le i p hpq hstart' hend'
  }⟩
  · simpa only [Nat.add_mul, one_mul] using hend'
  · intro r hr
    exact RingHom.mem_ker.mp (hpq hr)

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
              (extensionCurve L.lattice η z)), Nonempty (ChartProlongationMultiplicityData L S Q U (e c))) ∧
            (∑ c ∈ X.image (fun z => (linearTranslationImage L.lattice η W).mkQ
                (extensionCurve L.lattice η z)), (e c : ℝ)) ≤
              C * (if (∀ v ∈ linearTranslationDirections W, v 0 = 0) then (m : ℝ) else 1) *
                (n : ℝ) ^ b := by
  classical
  obtain ⟨C, hC, hbudget⟩ := stabilizer_height_selection_degree_budget L D S
    hS hS_value hS_ne η hη
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X h0 Q hQ hne hhigh
  obtain ⟨W, b, hW, hWQ, hb, e, hcomponents, hsum⟩ :=
    hbudget m n U hm hn hU X h0 Q hQ hne hhigh
  refine ⟨W, b, hW, hWQ, hb, e, ?_, hsum⟩
  intro c hc
  obtain ⟨w⟩ := hcomponents c hc
  exact chart_selection_to_prolongation L S Q U (e c) w

