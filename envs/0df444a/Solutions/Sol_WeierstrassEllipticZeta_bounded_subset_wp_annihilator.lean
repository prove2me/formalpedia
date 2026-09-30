-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_wp_annihilator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T02:26:25.621179+00:00
-- url     : https://prove2.me/submissions/d437bb05-2535-4d4c-8050-eda08986405e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_wp_root_power_dvd_of_sigma_contact
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_wp_contact_polynomial
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.Algebra.Polynomial.Roots
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
              ∃ p : Polynomial ℂ, p ≠ 0 ∧
                ((2 * p.natDegree + ((U : ℕ) + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
                ∀ z ∈ Y, z ∉ G.L.lattice →
                  (Polynomial.X - Polynomial.C (G.L.weierstrassP z)) ^ ((U : ℕ) + 1) ∣ p
                := by
  obtain ⟨C, hC, hbound⟩ := WeierstrassEllipticZeta.bounded_subset_wp_contact_polynomial G
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  obtain ⟨p, hp, hdeg, hcontact⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  obtain ⟨hne, hadd⟩ := WeierstrassEllipticZeta.sigma_addition_from_differential G.L G.D
    (fun z hz => WeierstrassEllipticZeta.hasDerivAt_weierstrassZeta G.L z hz)
    (fun z v hz hv hzv => WeierstrassEllipticZeta.zeta_addition_formula G.L z v hz hv hzv)
  refine ⟨p, hp, hdeg, ?_⟩
  intro z hz hzl
  apply WeierstrassEllipticZeta.wp_root_power_dvd_of_sigma_contact G.L G.D hne
    (fun ω z hω hz => WeierstrassEllipticZeta.weierstrassZeta_add_period G.L ω z hω hz)
    hadd p z hzl (U : ℕ)
  intro j hj
  exact hcontact z hz hzl j (by omega)
