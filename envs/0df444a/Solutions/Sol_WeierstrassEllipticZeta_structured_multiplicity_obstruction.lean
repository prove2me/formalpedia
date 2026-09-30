-- Prove2me | solution 1 for WeierstrassEllipticZeta.structured_multiplicity_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T20:59:35.825927+00:00
-- url     : https://prove2.me/submissions/d5c7f18e-a95e-4ef2-806d-feb813858e03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_frontier_contact_order
import Theorems.Thm_WeierstrassEllipticZeta_finite_order_multiplicity_obstruction
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
              extensionChartNormalize c Q ∉ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                (extensionChartCoordinates G.S c z) (G.B (m + 2 * n))) →
            (∀ (c : Fin 2) (k : ℕ),
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q)).totalDegree ≤
                m + 2 * n + k) →
            Frontier.HasChartCertificates G m n U X Q →
            Frontier.SubgroupBound G C m n U X := by
  have hnext := WeierstrassEllipticZeta.finite_order_multiplicity_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hnonzero hdegree hcharts
  apply hbound m n U hm hn hU X hX Q hQ _ hdegree hcharts
  intro c z hz
  exact (WeierstrassEllipticZeta.frontier_contact_order G c
    (extensionChartNormalize c Q) z hz (G.B (m + 2 * n))).2.mp
      (hnonzero c z hz)

