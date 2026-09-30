-- Prove2me | solution 1 for WeierstrassEllipticZeta.time_eliminant_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T00:06:32.342123+00:00
-- url     : https://prove2.me/submissions/596616b8-9c78-4ac4-80fe-ca9749dce282
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_contact_quotient_eliminant
import Theorems.Thm_WeierstrassEllipticZeta_contact_quotient_dimension_obstruction
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
            ((∃ P : Polynomial ℂ, P ≠ 0 ∧
              (P.natDegree : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              ∀ x ∈ X, ∀ k < U + 1, (Polynomial.derivative^[k] P).eval x = 0) ∨
              ((U + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  have hnext := WeierstrassEllipticZeta.contact_quotient_dimension_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hquot | hperiod
  · obtain ⟨J, hfinite, hqdim, hcontact⟩ := hquot
    obtain ⟨P, hmonic, hdeg, hjets⟩ :=
      WeierstrassEllipticZeta.contact_quotient_eliminant G X (U + 1) J hfinite hcontact
    refine Or.inl ⟨P, hmonic.ne_zero, ?_, hjets⟩
    rwa [hdeg]
  · exact Or.inr hperiod
