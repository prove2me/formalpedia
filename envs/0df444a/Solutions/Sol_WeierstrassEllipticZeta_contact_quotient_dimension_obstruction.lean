-- Prove2me | solution 1 for WeierstrassEllipticZeta.contact_quotient_dimension_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T00:45:45.606286+00:00
-- url     : https://prove2.me/submissions/2aa4bda5-d182-4a16-862d-e49ac192a871
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_admissible_contact_weight
import Theorems.Thm_WeierstrassEllipticZeta_finite_weight_contact_quotient_obstruction
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem solution (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
          1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                (extensionChartNormalize c Q)
              ∃! k : ℕ, k < G.B (m + 2 * n) ∧
                (z ∈ X + X + X → 3 * U + 1 ≤ k) ∧
                (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
                ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
                  f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n U X Q →
            ((∃ J : Fin 2 → Ideal (MvPolynomial (Fin 4) ℂ),
              (∀ c, FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c)) ∧
              ((∑ c : Fin 2, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) : ℕ) : ℝ) ≤
                C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              ∀ x ∈ X, ∃ c : Fin 2,
                G.S (extensionChartDenominator c) x ≠ 0 ∧
                J c ≤ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x) (U + 1)) ∨
              ((U + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  have hnext := WeierstrassEllipticZeta.finite_weight_contact_quotient_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  have hw := WeierstrassEllipticZeta.admissible_contact_weight G m n U X hX Q hcharts
  exact hbound m n ⟨U, Nat.lt_succ_of_le hw.2⟩ hm hn hU X hX Q hQ hlocal hdegree hcharts
