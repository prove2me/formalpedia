-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_formal_series_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T18:32:06.932247+00:00
-- url     : https://prove2.me/submissions/6e9ae424-5871-4398-a3b4-4e7f49d980c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_derivation_formal_flow_unique
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_elliptic_formal_flow_obstruction
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

private lemma elliptic_formal_ode_iff
    (g₂ g₃ : ℂ) (H : Fin 4 → PowerSeries ℂ) :
    (∀ a, PowerSeries.derivative ℂ (H a) = MvPolynomial.aeval H
      (extensionChartDerivation g₂ g₃ 0 (MvPolynomial.X a))) ↔
    PowerSeries.derivative ℂ (H 0) = 1 ∧
      PowerSeries.derivative ℂ (H 1) = H 2 ∧
      PowerSeries.derivative ℂ (H 2) =
        PowerSeries.C 6 * (H 1) ^ 2 - PowerSeries.C (g₂ / 2) ∧
      PowerSeries.derivative ℂ (H 3) = -H 1 := by
  constructor
  · intro h
    have h' := And.intro (h 0) (And.intro (h 1) (And.intro (h 2) (h 3)))
    simpa [extensionChartDerivation] using h'
  · rintro ⟨h0, h1, h2, h3⟩ a
    fin_cases a
    · simpa [extensionChartDerivation] using h0
    · simpa [extensionChartDerivation] using h1
    · simpa [extensionChartDerivation] using h2
    · simpa [extensionChartDerivation] using h3

theorem solution (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, ∀ U : Fin ((G.B (m + 2 * n) - 2) / 3 + 1),
          1 ≤ m → 1 ≤ n → 1 ≤ (U : ℕ) → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * (U : ℕ) + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n (U : ℕ) X Q →
            ∀ Y : Finset ℂ, Y ⊆ X → 0 ∈ Y →
              Y.card = ⌊(C * (m : ℝ) * (n : ℝ) ^ 2) /
                (((U : ℕ) + 1 : ℕ) : ℝ)⌋₊ + 1 →
              let Z := Y.filter (fun z => z ∉ G.L.lattice)
              let N := 3 * (U : ℕ) + 1
              let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
                ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
                  (extensionChartCoordinates G.S 0 z.val) N
              let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
              let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
              let φ : Polynomial ℂ →+* L :=
                (algebraMap (FractionRing (Polynomial ℂ)) L).comp
                  (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
              let J : Z → Fin 4 → PowerSeries ℂ := fun r a => PowerSeries.mk fun k =>
                MvPolynomial.eval (extensionChartCoordinates G.S 0 r.val)
                  ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[k]
                    (MvPolynomial.X a)) / (k.factorial : ℂ)
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I p) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      PowerSeries.coeff r.2.val
                        ((J r.1 (1 : Fin 4)) ^ j * (MvPolynomial.aeval (J r.1) p) ^ i) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_elliptic_formal_flow_obstruction G
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let J : Z → Fin 4 → PowerSeries ℂ := fun r a => PowerSeries.mk fun k =>
    MvPolynomial.eval (extensionChartCoordinates G.S 0 r.val)
      ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[k] (MvPolynomial.X a)) /
        (k.factorial : ℂ)
  exact hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard J
    (fun r => (TranscendenceTheory.derivation_formal_flow_unique ℂ (Fin 4)
      (extensionChartDerivation G.L.g₂ G.L.g₃ 0)
      (extensionChartCoordinates G.S 0 r.val)).1)
    (fun r => (elliptic_formal_ode_iff G.L.g₂ G.L.g₃ (J r)).1
      (TranscendenceTheory.derivation_formal_flow_unique ℂ (Fin 4)
        (extensionChartDerivation G.L.g₂ G.L.g₃ 0)
        (extensionChartCoordinates G.S 0 r.val)).2.1)
