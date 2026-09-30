-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_rational_generating_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T21:36:39.20605+00:00
-- url     : https://prove2.me/submissions/4007517c-7fe8-42d5-b22c-0abf73e138e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_iterated_power_series_swap
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_local_jet_generating_obstruction
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

private lemma swap_C {R : Type*} [Semiring R]
    (τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R))
    (hτ : ∀ f i k, PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
      PowerSeries.coeff k (PowerSeries.coeff i f)) (f : PowerSeries R) :
    τ (PowerSeries.C f) = PowerSeries.map PowerSeries.C f := by
  ext k i
  rw [hτ]
  by_cases hi : i = 0 <;> simp [PowerSeries.coeff_C, hi]

private lemma swap_X {R : Type*} [Semiring R]
    (τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R))
    (hτ : ∀ f i k, PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
      PowerSeries.coeff k (PowerSeries.coeff i f)) :
    τ PowerSeries.X = PowerSeries.C (PowerSeries.X : PowerSeries R) := by
  ext k i
  rw [hτ]
  by_cases hi : i = 1 <;> by_cases hk : k = 0 <;>
    simp [PowerSeries.coeff_X, PowerSeries.coeff_C, PowerSeries.coeff_one, hi, hk]

private lemma swap_inverse {R : Type*} [Ring R]
    (τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R))
    (hτ : ∀ f i k, PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
      PowerSeries.coeff k (PowerSeries.coeff i f))
    (d a b : PowerSeries R) :
    let ψ := PowerSeries.map (PowerSeries.C : R →+* PowerSeries R)
    let W := PowerSeries.C (PowerSeries.X : PowerSeries R)
    let H := PowerSeries.invOfUnit
      (1 - PowerSeries.C (2 * a) * PowerSeries.X +
        PowerSeries.C (a ^ 2 - d * b ^ 2) * PowerSeries.X ^ 2)
      (1 : (PowerSeries R)ˣ)
    (1 - ψ (2 * a) * W + ψ (a ^ 2 - d * b ^ 2) * W ^ 2) * τ H = 1 := by
  dsimp only
  have hinv := PowerSeries.mul_invOfUnit
    (1 - PowerSeries.C (2 * a) * PowerSeries.X +
      PowerSeries.C (a ^ 2 - d * b ^ 2) * PowerSeries.X ^ 2)
    (1 : (PowerSeries R)ˣ) (by simp)
  simpa only [map_mul, map_add, map_sub, map_one, map_pow,
    swap_C τ hτ, swap_X τ hτ] using congrArg τ hinv

private lemma swap_local_coeff {R : Type*} [Ring R]
    (τ : PowerSeries (PowerSeries R) ≃+* PowerSeries (PowerSeries R))
    (hτ : ∀ f i k, PowerSeries.coeff i (PowerSeries.coeff k (τ f)) =
      PowerSeries.coeff k (PowerSeries.coeff i f))
    (f y a b : PowerSeries R) (H : PowerSeries (PowerSeries R)) (i k : ℕ) :
    let ψ := PowerSeries.map (PowerSeries.C : R →+* PowerSeries R)
    let W := PowerSeries.C (PowerSeries.X : PowerSeries R)
    PowerSeries.coeff i (PowerSeries.coeff k
      (ψ f * ((1 - ψ a * W) * τ H + ψ y * (ψ b * W * τ H)))) =
    PowerSeries.coeff k (f *
      (PowerSeries.coeff i ((1 - PowerSeries.C a * PowerSeries.X) * H) +
        y * PowerSeries.coeff i (PowerSeries.C b * PowerSeries.X * H))) := by
  have h := hτ (PowerSeries.C f *
    ((1 - PowerSeries.C a * PowerSeries.X) * H +
      PowerSeries.C y * (PowerSeries.C b * PowerSeries.X * H))) i k
  simpa only [map_mul, map_add, map_sub, map_one, swap_C τ hτ, swap_X τ hτ,
    PowerSeries.coeff_C_mul] using h

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
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I (ρ p)) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      PowerSeries.coeff r.2.val
                        ((J r.1 (1 : Fin 4)) ^ j * (PowerSeries.coeff i
                          ((1 - PowerSeries.C (A p r.1) * PowerSeries.X) * H p r.1) +
                          J r.1 (2 : Fin 4) * PowerSeries.coeff i
                            (PowerSeries.C (B p r.1) * PowerSeries.X * H p r.1))) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  obtain ⟨τ, hτ, _⟩ := TranscendenceTheory.iterated_power_series_swap ℂ
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_local_jet_generating_obstruction G
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
  intro hnorm
  let ψ : PowerSeries ℂ →+* PowerSeries (PowerSeries ℂ) :=
    PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ)
  let W : PowerSeries (PowerSeries ℂ) := PowerSeries.C (PowerSeries.X : PowerSeries ℂ)
  let K : MvPolynomial (Fin 4) ℂ → Z → PowerSeries (PowerSeries ℂ) := fun p r => τ (H p r)
  let E : MvPolynomial (Fin 4) ℂ → Z → ℕ → PowerSeries (PowerSeries ℂ) :=
    fun p r j => ψ ((J r (1 : Fin 4)) ^ j) *
      ((1 - ψ (A p r) * W) * K p r +
        ψ (J r (2 : Fin 4)) * (ψ (B p r) * W * K p r))
  have heq (p : MvPolynomial (Fin 4) ℂ) (r : Z) (j i k : ℕ) :
      PowerSeries.coeff i (PowerSeries.coeff k (E p r j)) =
        PowerSeries.coeff k ((J r (1 : Fin 4)) ^ j *
          (PowerSeries.coeff i ((1 - PowerSeries.C (A p r) * PowerSeries.X) * H p r) +
            J r 2 * PowerSeries.coeff i (PowerSeries.C (B p r) * PowerSeries.X * H p r))) :=
    swap_local_coeff τ hτ ((J r 1) ^ j) (J r 2) (A p r) (B p r) (H p r) i k
  have hdenom (p : MvPolynomial (Fin 4) ℂ) (r : Z) :
      (1 - ψ (2 * A p r) * W + ψ (A p r ^ 2 - D r * B p r ^ 2) * W ^ 2) * K p r = 1 :=
    swap_inverse τ hτ (D r) (A p r) (B p r)
  obtain ⟨p, F, a, b, s, hFpos, hF, hFx, hroots, hcost⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
      hI P hinit hsecond hcurve ρ hρ hnorm τ hτ hdenom
  refine ⟨p, F, a, b, s, hFpos, hF, hFx, ?_, hcost⟩
  intro z hz hw
  apply hroots z hz
  obtain ⟨w, hw⟩ := hw
  refine ⟨w, ?_⟩
  intro i hi j hj
  change (∑ r : Z × Fin N,
    PowerSeries.coeff i (PowerSeries.coeff r.2.val (E p r.1 j)) • w r) = _
  calc
    _ = ∑ r : Z × Fin N, PowerSeries.coeff r.2.val
        ((J r.1 (1 : Fin 4)) ^ j *
          (PowerSeries.coeff i ((1 - PowerSeries.C (A p r.1) * PowerSeries.X) * H p r.1) +
            J r.1 2 * PowerSeries.coeff i (PowerSeries.C (B p r.1) * PowerSeries.X * H p r.1))) • w r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [heq]
    _ = _ := hw i hi j hj
