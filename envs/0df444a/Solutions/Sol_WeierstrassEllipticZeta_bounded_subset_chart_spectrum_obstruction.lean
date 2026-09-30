-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_chart_spectrum_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T16:33:02.234735+00:00
-- url     : https://prove2.me/submissions/d95ea10a-d94d-4a17-8e44-3a0ceffa294c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_transcendental_interpolation_descent
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_scalar_interpolation_obstruction
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.MvPolynomial.PDeriv
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
              (Ideal.span ({extensionChartCubic G.L.g₂ G.L.g₃ 0} :
                Set (MvPolynomial (Fin 4) ℂ)) ≤ I) →
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
                (∀ r, (PowerSeries.derivative ℂ (P r)) ^ 2 =
                  PowerSeries.C 4 * (P r) ^ 3 - PowerSeries.C G.L.g₂ * P r -
                    PowerSeries.C G.L.g₃) →
              let J : Z → Fin 4 → PowerSeries ℂ := fun r =>
                ![PowerSeries.C (v r 0) + PowerSeries.X, P r, PowerSeries.derivative ℂ (P r),
                  PowerSeries.mk fun k =>
                    if k = 0 then v r 3 else -PowerSeries.coeff (k - 1) (P r) / (k : ℂ)]
              ∀ ρ : MvPolynomial (Fin 4) ℂ → MvPolynomial (Fin 4) ℂ,
                (∀ p, (ρ p).degreeOf (2 : Fin 4) ≤ 1 ∧ p - ρ p ∈
                  Ideal.span ({extensionChartCubic G.L.g₂ G.L.g₃ 0} :
                    Set (MvPolynomial (Fin 4) ℂ))) →
              let D : Z → PowerSeries ℂ := fun r =>
                PowerSeries.C 4 * (P r) ^ 3 - PowerSeries.C G.L.g₂ * P r -
                  PowerSeries.C G.L.g₃
              let A : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
                MvPolynomial.aeval (Function.update (J r) (2 : Fin 4) 0) (ρ p)
              let B : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
                MvPolynomial.aeval (Function.update (J r) (2 : Fin 4) 0)
                  (MvPolynomial.pderiv (2 : Fin 4) (ρ p))
              let T : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries ℂ × PowerSeries ℂ :=
                fun p r => Nat.rec (1, 0)
                  (fun _ t => (A p r * t.1 + D r * B p r * t.2,
                    B p r * t.1 + A p r * t.2))
              (∀ p r i, (T p r i).1 ^ 2 - D r * (T p r i).2 ^ 2 =
                (A p r ^ 2 - D r * B p r ^ 2) ^ i) →
              let H : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r =>
                PowerSeries.invOfUnit
                  (1 - PowerSeries.C (2 * A p r) * PowerSeries.X +
                    PowerSeries.C (A p r ^ 2 - D r * B p r ^ 2) * PowerSeries.X ^ 2)
                  (1 : (PowerSeries ℂ)ˣ)
              ∀ τ : PowerSeries (PowerSeries ℂ) ≃+* PowerSeries (PowerSeries ℂ),
                (∀ (f : PowerSeries (PowerSeries ℂ)) (i k : ℕ),
                  PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
                    PowerSeries.coeff k (PowerSeries.coeff i f)) →
              let ψ : PowerSeries ℂ →+* PowerSeries (PowerSeries ℂ) :=
                PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ)
              let W : PowerSeries (PowerSeries ℂ) := PowerSeries.C (PowerSeries.X : PowerSeries ℂ)
              let K : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r => τ (H p r)
              (∀ p r, (1 - ψ (2 * A p r) * W +
                ψ (A p r ^ 2 - D r * B p r ^ 2) * W ^ 2) * K p r = 1) →
              let E : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries (PowerSeries ℂ) :=
                fun p r j => ψ ((J r (1 : Fin 4)) ^ j) *
                  ((1 - ψ (A p r) * W) * K p r +
                    ψ (J r (2 : Fin 4)) * (ψ (B p r) * W * K p r))
              let q : MvPolynomial (Fin 4) ℂ → Z → Polynomial ℂ := fun p r =>
                1 - Polynomial.C (PowerSeries.coeff 0 (2 * A p r)) * Polynomial.X +
                  Polynomial.C (PowerSeries.coeff 0 (A p r ^ 2 - D r * B p r ^ 2)) * Polynomial.X ^ 2
              let H₀ : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
                PowerSeries.invOfUnit (q p r : PowerSeries ℂ) (1 : ℂˣ)
              ∀ M : MvPolynomial (Fin 4) ℂ → Z → ℕ → ℕ → Polynomial ℂ,
                (∀ p r j k, (M p r j k).natDegree ≤ 2 * k + 1 ∧
                  PowerSeries.coeff k (E p r j) =
                    (M p r j k : PowerSeries ℂ) * H₀ p r ^ (k + 1)) →
              let Ω : MvPolynomial (Fin 4) ℂ → Polynomial ℂ := fun p => ∏ r : Z, q p r ^ N
              let H₁ : MvPolynomial (Fin 4) ℂ → PowerSeries ℂ := fun p => ∏ r : Z, H₀ p r ^ N
              (∀ p, (Ω p).natDegree ≤ 2 * N * Z.card ∧ (Ω p : PowerSeries ℂ) * H₁ p = 1) →
              ∀ V : MvPolynomial (Fin 4) ℂ → Z → ℕ → Fin N → Polynomial ℂ,
                (∀ p r j k, (V p r j k).natDegree < 2 * N * Z.card ∧
                  (M p r j k.val : PowerSeries ℂ) * H₀ p r ^ (k.val + 1) =
                    (V p r j k : PowerSeries ℂ) * H₁ p) →
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I (ρ p)) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  (s < 2 * N * Z.card ∨ ∃ r : Z,
                    z = algebraMap ℂ L (MvPolynomial.aeval (v r) p) ∨
                      z = algebraMap ℂ L
                        (MvPolynomial.aeval
                          (Function.update (v r) (2 : Fin 4) (-v r 2)) p)) →
                  ¬ ∃ w : Z × Fin N → L, ∀ j ≤ b,
                    if s < 2 * N * Z.card then
                      Polynomial.X ^ (s + 1) ∣
                        (1 - Polynomial.C z * Polynomial.X) *
                          (∑ r : Z × Fin N, Polynomial.C (w r) *
                            (V p r.1 j r.2).map (algebraMap ℂ L)) -
                          Polynomial.C ((φ Polynomial.X) ^ j) *
                            (Ω p).map (algebraMap ℂ L)
                    else
                      (1 - Polynomial.C z * Polynomial.X) *
                        (∑ r : Z × Fin N, Polynomial.C (w r) *
                          (V p r.1 j r.2).map (algebraMap ℂ L)) =
                        Polynomial.C ((φ Polynomial.X) ^ j) *
                          (Ω p).map (algebraMap ℂ L)) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_scalar_interpolation_obstruction G
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let N := 3 * (U : ℕ) + 1
  let v : Z → Fin 4 → ℂ := fun r => extensionChartCoordinates G.S 0 r.val
  dsimp only
  intro hI P hinit hsecond hcurve ρ hρ
  let J : Z → Fin 4 → PowerSeries ℂ := fun r =>
    ![PowerSeries.C (v r 0) + PowerSeries.X, P r, PowerSeries.derivative ℂ (P r),
      PowerSeries.mk fun k =>
        if k = 0 then v r 3 else -PowerSeries.coeff (k - 1) (P r) / (k : ℂ)]
  let D : Z → PowerSeries ℂ := fun r =>
    PowerSeries.C 4 * (P r) ^ 3 - PowerSeries.C G.L.g₂ * P r - PowerSeries.C G.L.g₃
  let A : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
    MvPolynomial.aeval (Function.update (J r) (2 : Fin 4) 0) (ρ p)
  let B : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
    MvPolynomial.aeval (Function.update (J r) (2 : Fin 4) 0)
      (MvPolynomial.pderiv (2 : Fin 4) (ρ p))
  let T : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries ℂ × PowerSeries ℂ :=
    fun p r => Nat.rec (1, 0)
      (fun _ t => (A p r * t.1 + D r * B p r * t.2, B p r * t.1 + A p r * t.2))
  let H : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r =>
    PowerSeries.invOfUnit
      (1 - PowerSeries.C (2 * A p r) * PowerSeries.X +
        PowerSeries.C (A p r ^ 2 - D r * B p r ^ 2) * PowerSeries.X ^ 2)
      (1 : (PowerSeries ℂ)ˣ)
  intro hnorm τ hτ hdenom M hM hΩ V hV
  let ψ : PowerSeries ℂ →+* PowerSeries (PowerSeries ℂ) :=
    PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ)
  let W : PowerSeries (PowerSeries ℂ) := PowerSeries.C (PowerSeries.X : PowerSeries ℂ)
  let K : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r => τ (H p r)
  let E : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries (PowerSeries ℂ) :=
    fun p r j => ψ ((J r (1 : Fin 4)) ^ j) *
      ((1 - ψ (A p r) * W) * K p r +
        ψ (J r (2 : Fin 4)) * (ψ (B p r) * W * K p r))
  let q : MvPolynomial (Fin 4) ℂ → Z → Polynomial ℂ := fun p r =>
    1 - Polynomial.C (PowerSeries.coeff 0 (2 * A p r)) * Polynomial.X +
      Polynomial.C (PowerSeries.coeff 0 (A p r ^ 2 - D r * B p r ^ 2)) * Polynomial.X ^ 2
  let H₀ : MvPolynomial (Fin 4) ℂ → Z → PowerSeries ℂ := fun p r =>
    PowerSeries.invOfUnit (q p r : PowerSeries ℂ) (1 : ℂˣ)
  let Ω : MvPolynomial (Fin 4) ℂ → Polynomial ℂ := fun p => ∏ r : Z, q p r ^ N
  let H₁ : MvPolynomial (Fin 4) ℂ → PowerSeries ℂ := fun p => ∏ r : Z, H₀ p r ^ N
  let L := AlgebraicClosure (FractionRing (Polynomial ℂ))
  let φ : Polynomial ℂ →+* L :=
    (algebraMap (FractionRing (Polynomial ℂ)) L).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  obtain ⟨p, F, a, b, s, hFpos, hF, hFx, hroots, hcost⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
      hI P hinit hsecond hcurve ρ hρ hnorm τ hτ hdenom M hM hΩ V hV
  let Φ : Polynomial ℂ →ₐ[ℂ] L :=
    (IsScalarTower.toAlgHom ℂ (FractionRing (Polynomial ℂ)) L).comp
      (IsScalarTower.toAlgHom ℂ (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  have hΦ : Function.Injective Φ :=
    (RingHom.injective (algebraMap (FractionRing (Polynomial ℂ)) L)).comp
      (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  have hΦX : Φ Polynomial.X = φ Polynomial.X := rfl
  have hdescent (c : ℂ) :=
    TranscendenceTheory.transcendental_interpolation_descent ℂ L (Z × Fin N)
      Φ hΦ b c (fun r j => V p r.1 j r.2) (Ω p)
  refine ⟨p, F, a, b, s, hFpos, hF, hFx, ?_, hcost⟩
  intro z hz hguard hweights
  have hroot := hroots z hz hguard
  by_cases hs : s < 2 * (3 * (U : ℕ) + 1) * (Y.filter (fun z => z ∉ G.L.lattice)).card
  · simp only [if_pos hs] at hroot
    apply hroot
    obtain ⟨w, hw⟩ := hweights
    exact ⟨w, fun j hj => by simpa only [if_pos hs] using hw j hj⟩
  · simp only [if_neg hs] at hroot
    obtain ⟨r, hr | hr⟩ := hguard.resolve_left hs
    all_goals
      obtain ⟨k, hk, hno⟩ := hroot _ hr
      apply hno
      apply (hdescent _).mp _ k hk
      obtain ⟨w, hw⟩ := hweights
      refine ⟨w, ?_⟩
      intro j hj
      simpa only [if_neg hs, hr, hΦX] using hw j hj
