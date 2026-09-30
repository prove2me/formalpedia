-- Prove2me | solution 1 for WeierstrassEllipticZeta.canonical_box_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T21:59:12.598145+00:00
-- url     : https://prove2.me/submissions/455861c6-7849-4b49-825f-5cc5452401e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_normalized_jet_contact_certificate
import Theorems.Thm_WeierstrassEllipticZeta_normalized_jet_weight_contact_obstruction
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
              ∃ p : Fin 2 → MvPolynomial (Fin 4) ℂ,
              ((∑ c : Fin 2, ∑ i : Fin 4,
                (p c).degreeOf i * ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
                  max ((p c).degreeOf j + 1)
                    (((U : ℕ) + 1) *
                      (Finset.univ.image (fun x : {z : X // a z = c} =>
                        (extensionChartCoordinates G.S c x.val.val) j)).card) : ℕ) : ℝ) ≤ C * (m : ℝ) * (n : ℝ) ^ 2 ∧
              (∀ c : Fin 2, p c ≠ 0) ∧
              (∀ c : Fin 2, ∀ x : {z : X // a z = c},
                p c ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
                  (extensionChartCoordinates G.S c x.val.val) ((U : ℕ) + 1))) ∨
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (X : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2) := by
  classical
  have hnext := WeierstrassEllipticZeta.normalized_jet_weight_contact_obstruction G
  rcases hnext with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts
  rcases hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts with hjet | hperiod
  · obtain ⟨a, hvalid, k, hcount⟩ := hjet
    let p (c : Fin 2) : MvPolynomial (Fin 4) ℂ :=
      if Nonempty {z : X // a z = c} then
        (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[(k c).val]
          (extensionChartNormalize c Q)
      else 1
    have hcert (c : Fin 2) := WeierstrassEllipticZeta.normalized_jet_contact_certificate
      G m n (U : ℕ) X hX Q hcharts c (k c).val (Nat.le_of_lt_succ (k c).isLt)
    have hvalid' (c : Fin 2) (x : {z : X // a z = c}) :
        G.S (extensionChartDenominator c) x.val.val ≠ 0 := by
      simpa only [x.property] using hvalid x.val
    refine Or.inl ⟨a, hvalid, p, hcount, ?_, ?_⟩
    · intro c
      by_cases hc : Nonempty {z : X // a z = c}
      · obtain ⟨x⟩ := hc
        have hn := (hcert c).2 ⟨x.val.val, x.val.property, hvalid' c x⟩
        simpa only [p, if_pos (show Nonempty {z : X // a z = c} from ⟨x⟩)] using hn
      · simpa only [p, if_neg hc] using (one_ne_zero : (1 : MvPolynomial (Fin 4) ℂ) ≠ 0)
    · intro c x
      have hx := (hcert c).1 x.val.val x.val.property (hvalid' c x)
      simpa only [p, if_pos (show Nonempty {z : X // a z = c} from ⟨x⟩)] using hx
  · exact Or.inr hperiod
