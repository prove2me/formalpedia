-- Prove2me | solution 1 for WeierstrassEllipticZeta.time_coordinate_cardinality_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T23:04:38.426539+00:00
-- url     : https://prove2.me/submissions/c5fc6f04-01cd-4161-8e69-f8e9af234df2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_pointed_cardinality_image_test_iff
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_period_contact_obstruction
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
            (((((U : ℕ) + 1) * X.card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  classical
  have hnext := WeierstrassEllipticZeta.bounded_subset_period_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : 0 ≤ C * (n : ℝ) ^ 2 := mul_nonneg hC.le (sq_nonneg _)
  have hBA : C * (n : ℝ) ^ 2 ≤ C * (m : ℝ) * (n : ℝ) ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm' hC.le) (sq_nonneg (n : ℝ))
  have hw : (0 : ℝ) < (((U : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have h := (WeierstrassEllipticZeta.pointed_cardinality_image_test_iff
    G.L.lattice.mkQ X 0 hX (((U : ℕ) + 1 : ℕ) : ℝ)
      (C * (m : ℝ) * (n : ℝ) ^ 2) (C * (n : ℝ) ^ 2) hw hB hBA).mpr
        (hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts)
  simpa only [Nat.cast_mul] using h
