-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_period_contact_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T01:51:04.70449+00:00
-- url     : https://prove2.me/submissions/706f3b09-f2ea-4fb7-aa02-49c7c610316b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_period_image_multiplicity_le_of_wp_polynomial
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_annihilator
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_addition_data
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
            ∀ Y : Finset ℂ, Y ⊆ X → 0 ∈ Y →
              Y.card = ⌊(C * (m : ℝ) * (n : ℝ) ^ 2) /
                (((U : ℕ) + 1 : ℕ) : ℝ)⌋₊ + 1 →
              (((U : ℕ) + 1 : ℕ) : ℝ) * (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard ≤
                C * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_wp_annihilator G
  obtain ⟨D⟩ := WeierstrassEllipticZeta.exists_elliptic_sigma_addition_data G.L
    (WeierstrassEllipticZeta.hasDerivAt_weierstrassZeta G.L)
    (WeierstrassEllipticZeta.zeta_addition_formula G.L)
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  obtain ⟨p, hp, hdeg, hdiv⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  have hcount := WeierstrassEllipticZeta.period_image_multiplicity_le_of_wp_polynomial
    G.L D Y ((U : ℕ) + 1) p hp hdiv
  have hcount' : (((U : ℕ) + 1 : ℕ) : ℝ) *
      (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard ≤
        ((2 * p.natDegree + ((U : ℕ) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  exact hcount'.trans hdeg
