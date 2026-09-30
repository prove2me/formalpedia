-- Prove2me | solution 1 for WeierstrassEllipticZeta.monomial_reduction_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T02:18:21.548075+00:00
-- url     : https://prove2.me/submissions/a9141b39-ac63-488b-a340-23d0edb6df6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_monomial_border_completion
import Theorems.Thm_WeierstrassEllipticZeta_border_reduction_contact_obstruction
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
            ((∃ S : Fin 2 → Finset (Fin 4 →₀ ℕ),
              ∃ r : Fin 2 → Fin 4 → (Fin 4 →₀ ℕ) → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, (S c).card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, 0 ∈ S c) ∧
              (∀ (c : Fin 2) (i : Fin 4), ∀ d ∈ S c, (r c i d).support ⊆ S c) ∧
              ∀ x ∈ X, ∃ c : Fin 2,
                G.S (extensionChartDenominator c) x ≠ 0 ∧
                ∀ i : Fin 4, ∀ d ∈ S c,
                  MvPolynomial.X i * MvPolynomial.monomial d 1 - r c i d ∈
                    extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                      (extensionChartCoordinates G.S c x) ((U : ℕ) + 1)) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  have hnext := WeierstrassEllipticZeta.border_reduction_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hborder | hperiod
  · obtain ⟨S, b, hcount, hzero, hsupport, hcontact⟩ := hborder
    have hcert (c : Fin 2) := WeierstrassEllipticZeta.monomial_border_completion
      ℂ (Fin 4) (S c) (b c) (hsupport c)
    choose r hsupp hmem using hcert
    refine Or.inl ⟨S, r, hcount, hzero, hsupp, ?_⟩
    intro x hx
    obtain ⟨c, hden, hrelations⟩ := hcontact x hx
    refine ⟨c, hden, ?_⟩
    exact (hmem c (extensionChartContactIdeal G.L.g₂ G.L.g₃ c
      (extensionChartCoordinates G.S c x) ((U : ℕ) + 1))).mp hrelations
  · exact Or.inr hperiod
