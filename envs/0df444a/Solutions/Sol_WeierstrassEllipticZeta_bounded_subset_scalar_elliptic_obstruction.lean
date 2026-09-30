-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_scalar_elliptic_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T19:41:40.677329+00:00
-- url     : https://prove2.me/submissions/890cdf3e-6364-4de9-9d16-6ec5b3ad4925
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeierstrassEllipticZeta_chart_cubic_in_all_contact_ideals
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_weierstrass_curve_obstruction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Choose
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

private lemma energy_constant_iff_weierstrass
    (g₂ g₃ x y : ℂ) (hc : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃)
    (P : PowerSeries ℂ) :
    ((PowerSeries.derivative ℂ P) ^ 2 - PowerSeries.C 4 * P ^ 3 +
      PowerSeries.C g₂ * P = PowerSeries.C (y ^ 2 - 4 * x ^ 3 + g₂ * x)) ↔
    (PowerSeries.derivative ℂ P) ^ 2 =
      PowerSeries.C 4 * P ^ 3 - PowerSeries.C g₂ * P - PowerSeries.C g₃ := by
  have hconst : y ^ 2 - 4 * x ^ 3 + g₂ * x = -g₃ := by linear_combination hc
  rw [hconst, map_neg]
  constructor <;> intro h <;> linear_combination h

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
              let Z := Y.filter (fun z => z ∉ G.L.lattice)
              let N := 3 * (U : ℕ) + 1
              let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
                ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
                  (extensionChartCoordinates G.S 0 z.val) N
              let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
              let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
              let φ : Polynomial ℂ →+* L :=
                (algebraMap (FractionRing (Polynomial ℂ)) L).comp
                  (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
              let v : Z → Fin 4 → ℂ := fun r => extensionChartCoordinates G.S 0 r.val
              ∀ P : Z → PowerSeries ℂ,
                (∀ r, PowerSeries.coeff 0 (P r) = v r 1 ∧
                  PowerSeries.coeff 1 (P r) = v r 2) →
                (∀ r, PowerSeries.derivative ℂ (PowerSeries.derivative ℂ (P r)) =
                  PowerSeries.C 6 * (P r) ^ 2 - PowerSeries.C (G.L.g₂ / 2)) →
                (∀ r, (PowerSeries.derivative ℂ (P r)) ^ 2 -
                  PowerSeries.C 4 * (P r) ^ 3 + PowerSeries.C G.L.g₂ * P r =
                    PowerSeries.C ((v r 2) ^ 2 - 4 * (v r 1) ^ 3 + G.L.g₂ * v r 1)) →
              let J : Z → Fin 4 → PowerSeries ℂ := fun r =>
                ![PowerSeries.C (v r 0) + PowerSeries.X, P r, PowerSeries.derivative ℂ (P r),
                  PowerSeries.mk fun k =>
                    if k = 0 then v r 3 else -PowerSeries.coeff (k - 1) (P r) / (k : ℂ)]
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I p) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      PowerSeries.coeff r.2.val
                        ((J r.1 (1 : Fin 4)) ^ j * (MvPolynomial.aeval (J r.1) p) ^ i) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_weierstrass_curve_obstruction G
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let N := 3 * (U : ℕ) + 1
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
      (extensionChartCoordinates G.S 0 z.val) N
  let v : Z → Fin 4 → ℂ := fun r => extensionChartCoordinates G.S 0 r.val
  have hI : Ideal.span ({extensionChartCubic G.L.g₂ G.L.g₃ 0} :
      Set (MvPolynomial (Fin 4) ℂ)) ≤ I := by
    apply le_iInf
    intro r
    exact (WeierstrassEllipticZeta.chart_cubic_in_all_contact_ideals G r.val
      (Finset.mem_filter.mp r.property).2).2 N
  dsimp only
  intro P hinit hsecond henergy
  exact hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
    hI P hinit hsecond (fun r =>
      (energy_constant_iff_weierstrass G.L.g₂ G.L.g₃ (v r 1) (v r 2)
        (WeierstrassEllipticZeta.chart_cubic_in_all_contact_ideals G r.val
          (Finset.mem_filter.mp r.property).2).1 (P r)).1 (henergy r))
