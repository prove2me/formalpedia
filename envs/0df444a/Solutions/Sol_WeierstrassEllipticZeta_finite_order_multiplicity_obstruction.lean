-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_order_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T22:38:18.818969+00:00
-- url     : https://prove2.me/submissions/e78a7693-c9ab-48de-9b38-6d6cc01f1c46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_frontier_local_multiplicity
import Theorems.Thm_WeierstrassEllipticZeta_germ_multiplicity_obstruction
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
open WeierstrassEllipticZeta
open scoped Classical

theorem solution (G : Frontier.Geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
          1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
          0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
            (∀ d ∈ Q.support, d 0 + d 1 = m ∧
              d 2 + d 3 + d 4 + d 5 + d 6 = n) →
            (∀ (c : Fin 2) (z : ℂ), G.S (extensionChartDenominator c) z ≠ 0 →
              analyticOrderAt
                (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
                  (extensionChartNormalize c Q)) z < G.B (m + 2 * n)) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n U X Q →
            Frontier.SubgroupBound G C m n U X := by
  have hnext := WeierstrassEllipticZeta.germ_multiplicity_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hupper hdegree hcharts
  apply hbound m n U hm hn hU X hX Q hQ _ hdegree hcharts
  intro c z hz
  exact WeierstrassEllipticZeta.frontier_local_multiplicity
    G m n U X Q hcharts c z hz (hupper c z hz)
