-- Prove2me | solution 1 for WeierstrassEllipticZeta.frontier_contact_order
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T20:59:35.252852+00:00
-- url     : https://prove2.me/submissions/5c946188-bf6d-4df2-a3ae-061d0db4d94d

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry

open WeierstrassEllipticZeta

/-- Convert contact-ideal membership to the analytic order along the actual curve. -/
theorem solution
    (G : Frontier.Geometry) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
    (z : ℂ) (hz : G.S (extensionChartDenominator c) z ≠ 0) (k : ℕ) :
    (p ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z) k ↔
      (k : ℕ∞) ≤ analyticOrderAt
        (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w) p) z) ∧
    (p ∉ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z) k ↔
      analyticOrderAt
        (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w) p) z < k) := by
  have hmem := G.hcontact.1 c (extensionChartCoordinates G.S c z) k p
  have horder := (G.hjets.2 c p k).2 z hz
  have hiff := hmem.trans horder.2.symm
  exact ⟨hiff, by simpa only [not_le] using not_congr hiff⟩
