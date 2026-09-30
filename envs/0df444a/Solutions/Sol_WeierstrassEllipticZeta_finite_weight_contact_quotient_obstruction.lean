-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_weight_contact_quotient_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T01:21:29.489062+00:00
-- url     : https://prove2.me/submissions/f60ff09f-fd79-4d94-89e4-97e625bbb882
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_coordinate_stable_quotient_bound
import Theorems.Thm_WeierstrassEllipticZeta_stable_span_contact_quotient_obstruction
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
              (∀ c, FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c)) ∧
              ((∑ c : Fin 2, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) : ℕ) : ℝ) ≤
                C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              ∀ x ∈ X, ∃ c : Fin 2,
                G.S (extensionChartDenominator c) x ≠ 0 ∧
                J c ≤ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x) ((U : ℕ) + 1)) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  have hnext := WeierstrassEllipticZeta.stable_span_contact_quotient_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hspan | hperiod
  · obtain ⟨J, d, v, hcount, hstable, hcontact⟩ := hspan
    have hf (c : Fin 2) :=
      WeierstrassEllipticZeta.coordinate_stable_quotient_bound
        ℂ (Fin 4) (J c) (d c) (v c) (hstable c).1 (hstable c).2
    refine Or.inl ⟨J, fun c => (hf c).2.1, ?_, hcontact⟩
    have hdim : (∑ c : Fin 2, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c)) ≤
        ∑ c : Fin 2, d c := Finset.sum_le_sum (fun c _ => (hf c).2.2)
    have hdim' : ((∑ c : Fin 2, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J c) : ℕ) : ℝ) ≤
        ((∑ c : Fin 2, d c : ℕ) : ℝ) := by exact_mod_cast hdim
    exact hdim'.trans hcount
  · exact Or.inr hperiod
