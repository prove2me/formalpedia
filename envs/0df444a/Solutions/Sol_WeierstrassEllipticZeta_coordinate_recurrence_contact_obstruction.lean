-- Prove2me | solution 1 for WeierstrassEllipticZeta.coordinate_recurrence_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T20:48:47.399201+00:00
-- url     : https://prove2.me/submissions/809067ae-e9b4-40e5-aa35-6352c85a7281
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_finite_coordinate_power_recurrence
import Theorems.Thm_WeierstrassEllipticZeta_coordinate_value_count_contact_obstruction
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
            ((∃ a : X → Fin 2,
              (∀ x : X, G.S (extensionChartDenominator (a x)) x.val ≠ 0) ∧
              ∃ b : Fin 2 → (Fin 4 →₀ ℕ),
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  (b c j + 1) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ (c : Fin 2) (i : Fin 4), (p c).degreeOf i ≤ b c i) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1)) ∧
              ∃ r : Fin 2 → Fin 4 → MvPolynomial (Fin 4) ℂ,
              (∀ (c : Fin 2) (i : Fin 4), ∀ e ∈ (r c i).support,
                e ≤ Finsupp.single i (b c i)) ∧
              ∀ (c : Fin 2) (i : Fin 4), ∀ x : {z : X // a z = c},
                MvPolynomial.X i ^ (b c i + 1) - r c i ∈
                  extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                    (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1)) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  classical
  have hnext := WeierstrassEllipticZeta.coordinate_value_count_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hjet | hperiod
  · obtain ⟨a, hvalid, b, p, hcount, hne, hfit, hcontact, hvalues⟩ := hjet
    let T (c : Fin 2) (i : Fin 4) : Finset ℂ :=
      Finset.univ.image (fun x : {z : X // a z = c} =>
        (extensionChartCoordinates G.S c x.val.val) i)
    have hmake := fun (c : Fin 2) (i : Fin 4) =>
      WeierstrassEllipticZeta.finite_coordinate_power_recurrence
        ℂ (Fin 4) i (T c i) ((U : ℕ) + 1) (b c i) (hvalues c i)
    choose r hsupport hrec using hmake
    refine Or.inl ⟨a, hvalid, b, p, hcount, hne, hfit, hcontact, r, hsupport, ?_⟩
    intro c i x
    apply hrec c i (extensionChartCoordinates G.S c x.val.val) ?_
      (extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1))
      (G.hcontact.2.2.1 c (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1))
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · exact Or.inr hperiod
