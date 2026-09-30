-- Prove2me | solution 1 for WeierstrassEllipticZeta.border_reduction_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T02:35:37.609015+00:00
-- url     : https://prove2.me/submissions/48e40885-0d49-48f8-83b5-d79561d5ed9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_finite_jet_span_interpolation
import Theorems.Thm_WeierstrassEllipticZeta_border_jet_span_contact_obstruction
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
              let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
                (S c).image (fun d => d + Finsupp.single i 1)) \ S c
              ∃ b : Fin 2 → (Fin 4 →₀ ℕ) → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, (S c).card : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, 0 ∈ S c) ∧
              (∀ c : Fin 2, ∀ e ∈ B c, (b c e).support ⊆ S c) ∧
              ∀ x ∈ X, ∃ c : Fin 2,
                G.S (extensionChartDenominator c) x ≠ 0 ∧
                ∀ e ∈ B c, MvPolynomial.monomial e 1 - b c e ∈
                  extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                    (extensionChartCoordinates G.S c x) ((U : ℕ) + 1)) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  classical
  have hnext := WeierstrassEllipticZeta.border_jet_span_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hjet | hperiod
  · obtain ⟨a, hvalid, S, hcount, hzero, hspan⟩ := hjet
    let B := fun c : Fin 2 => (Finset.univ.biUnion fun i : Fin 4 =>
      (S c).image (fun d => d + Finsupp.single i 1)) \ S c
    have hchoices (c : Fin 2) (e : Fin 4 →₀ ℕ) :
        ∃ q : MvPolynomial (Fin 4) ℂ, e ∈ B c → q.support ⊆ S c ∧
          ∀ x : {z : X // a z = c}, ∀ k : Fin ((U : ℕ) + 1),
            MvPolynomial.eval (extensionChartCoordinates G.S c x.val.val)
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val]
                (MvPolynomial.monomial e 1 - q)) = 0 := by
      by_cases he : e ∈ B c
      · obtain ⟨q, hq, hz⟩ :=
          (WeierstrassEllipticZeta.finite_jet_span_interpolation
            ℂ (Fin 4) {z : X // a z = c} (extensionChartDerivation G.L.g₂ G.L.g₃ c)
            (fun x => extensionChartCoordinates G.S c x.val.val)
            ((U : ℕ) + 1) (S c) (MvPolynomial.monomial e 1)).mpr (hspan c e he)
        exact ⟨q, fun _ => ⟨hq, hz⟩⟩
      · exact ⟨0, fun h => (he h).elim⟩
    choose b hb using hchoices
    refine Or.inl ⟨S, b, hcount, hzero, ?_, ?_⟩
    · intro c e he
      exact (hb c e he).1
    · intro x hx
      let xx : X := ⟨x, hx⟩
      refine ⟨a xx, hvalid xx, ?_⟩
      intro e he
      apply (G.hcontact.1 _ _ _ _).mpr
      intro k hk
      exact (hb (a xx) e he).2 ⟨xx, rfl⟩ ⟨k, hk⟩
  · exact Or.inr hperiod
