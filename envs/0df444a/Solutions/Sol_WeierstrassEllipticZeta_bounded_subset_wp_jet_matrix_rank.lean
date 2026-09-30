-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_wp_jet_matrix_rank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T03:47:50.355375+00:00
-- url     : https://prove2.me/submissions/2d04f5d1-91ad-48d0-971d-292f6a5729d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_wp_chart_jet_univariate_formula
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_univariate_jet_rank
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
              let J : Matrix (Z × Fin N) (Fin (N * Z.card)) ℂ := Matrix.of fun r k =>
                MvPolynomial.eval (extensionChartCoordinates G.S 0 r.1.val)
                  ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[r.2.val]
                    (MvPolynomial.X (1 : Fin 4) ^ k.val))
              ((2 * J.rank + ((U : ℕ) + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := WeierstrassEllipticZeta.bounded_subset_wp_univariate_jet_rank G
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let N := 3 * (U : ℕ) + 1
  let T : Polynomial ℂ → Polynomial ℂ := fun q =>
    (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C G.L.g₂ * Polynomial.X -
      Polynomial.C G.L.g₃) * q.derivative.derivative +
    (Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C (G.L.g₂ / 2)) * q.derivative
  have hmat : (Matrix.of (fun r k =>
      MvPolynomial.eval (extensionChartCoordinates G.S 0 r.1.val)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[r.2.val]
          (MvPolynomial.X (1 : Fin 4) ^ k.val))) : Matrix (Z × Fin N) (Fin (N * Z.card)) ℂ) =
      Matrix.of (fun r k =>
        let q := T^[r.2.val / 2] (Polynomial.X ^ k.val)
        if r.2.val % 2 = 0 then q.eval (G.L.weierstrassP r.1.val)
        else G.L.derivWeierstrassP r.1.val * q.derivative.eval (G.L.weierstrassP r.1.val)) := by
    ext r k
    have h := (WeierstrassEllipticZeta.wp_chart_jet_univariate_formula G r.1.val
      (Finset.mem_filter.mp r.1.property).2 (Polynomial.X ^ k.val) r.2.val).2
    simpa only [Matrix.of_apply, map_pow, Polynomial.aeval_X] using h
  dsimp only
  rw [hmat]
  exact hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
