-- Prove2me | solution 1 for WeierstrassEllipticZeta.stable_span_contact_quotient_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T01:58:35.764418+00:00
-- url     : https://prove2.me/submissions/88d96113-273e-4c00-be62-7104dcfe8b9b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_monomial_reduction_stable_span
import Theorems.Thm_WeierstrassEllipticZeta_monomial_reduction_contact_obstruction
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
            ((∃ J : Fin 2 → Ideal (MvPolynomial (Fin 4) ℂ),
              ∃ d : Fin 2 → ℕ, ∃ v : (c : Fin 2) → Fin (d c) → MvPolynomial (Fin 4) ℂ ⧸ J c,
              ((∑ c : Fin 2, d c : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2,
                (1 : MvPolynomial (Fin 4) ℂ ⧸ J c) ∈ Submodule.span ℂ (Set.range (v c)) ∧
                ∀ i : Fin 4, ∀ j : Fin (d c),
                  Ideal.Quotient.mk (J c) (MvPolynomial.X i) * v c j ∈
                    Submodule.span ℂ (Set.range (v c))) ∧
              ∀ x ∈ X, ∃ c : Fin 2,
                G.S (extensionChartDenominator c) x ≠ 0 ∧
                J c ≤ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x) ((U : ℕ) + 1)) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  have hnext := WeierstrassEllipticZeta.monomial_reduction_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hred | hperiod
  · obtain ⟨S, r, hcount, hzero, hsupport, hcontact⟩ := hred
    let J : Fin 2 → Ideal (MvPolynomial (Fin 4) ℂ) := fun c => Ideal.span
      {p | ∃ i : Fin 4, ∃ d ∈ S c,
        p = MvPolynomial.X i * MvPolynomial.monomial d 1 - r c i d}
    have hcert (c : Fin 2) := WeierstrassEllipticZeta.monomial_reduction_stable_span
      ℂ (Fin 4) (S c) (hzero c) (r c) (hsupport c)
    choose v hv using hcert
    refine Or.inl ⟨J, fun c => (S c).card, v, hcount, hv, ?_⟩
    intro x hx
    obtain ⟨c, hden, hrel⟩ := hcontact x hx
    refine ⟨c, hden, Ideal.span_le.mpr ?_⟩
    rintro p ⟨i, d, hd, rfl⟩
    exact hrel i d hd
  · exact Or.inr hperiod
