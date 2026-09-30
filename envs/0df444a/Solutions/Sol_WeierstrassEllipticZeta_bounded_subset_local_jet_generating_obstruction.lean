-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_local_jet_generating_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T21:57:02.654236+00:00
-- url     : https://prove2.me/submissions/354d7a7a-67f8-4b29-bc3f-6094af0cbaa6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_formal_series_coefficient_denominator_bound
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_jet_denominator_obstruction
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

private lemma local_jet_fraction {R : Type*} [CommRing R]
    (f y a b d : PowerSeries R) (K : PowerSeries (PowerSeries R))
    (hK :
      (1 - PowerSeries.map PowerSeries.C (2 * a) * PowerSeries.C PowerSeries.X +
        PowerSeries.map PowerSeries.C (a ^ 2 - d * b ^ 2) *
          (PowerSeries.C PowerSeries.X) ^ 2) * K = 1) (k : ℕ) :
    let ψ := PowerSeries.map (PowerSeries.C : R →+* PowerSeries R)
    let W := PowerSeries.C (PowerSeries.X : PowerSeries R)
    let q : Polynomial R := 1 - Polynomial.C (PowerSeries.coeff 0 (2 * a)) * Polynomial.X +
      Polynomial.C (PowerSeries.coeff 0 (a ^ 2 - d * b ^ 2)) * Polynomial.X ^ 2
    let L := PowerSeries.invOfUnit (q : PowerSeries R) (1 : Rˣ)
    ∃ P : Polynomial R, P.natDegree ≤ 2 * k + 1 ∧
      PowerSeries.coeff k
        (ψ f * ((1 - ψ a * W) * K + ψ y * (ψ b * W * K))) =
          (P : PowerSeries R) * L ^ (k + 1) := by
  let ψ := PowerSeries.map (PowerSeries.C : R →+* PowerSeries R)
  let W := PowerSeries.C (PowerSeries.X : PowerSeries R)
  let ξ := PowerSeries.map (Polynomial.C : R →+* Polynomial R)
  let φ : Polynomial R →+* PowerSeries R := Polynomial.coeToPowerSeries.ringHom
  let Q : PowerSeries (Polynomial R) :=
    1 - ξ (2 * a) * PowerSeries.C Polynomial.X +
      ξ (a ^ 2 - d * b ^ 2) * PowerSeries.C (Polynomial.X ^ 2)
  let V : PowerSeries (Polynomial R) :=
    ξ f + ξ (f * (-a + y * b)) * PowerSeries.C Polynomial.X
  let E := ψ f * ((1 - ψ a * W) * K + ψ y * (ψ b * W * K))
  let q : Polynomial R := 1 - Polynomial.C (PowerSeries.coeff 0 (2 * a)) * Polynomial.X +
    Polynomial.C (PowerSeries.coeff 0 (a ^ 2 - d * b ^ 2)) * Polynomial.X ^ 2
  let L := PowerSeries.invOfUnit (q : PowerSeries R) (1 : Rˣ)
  have hm (g : PowerSeries R) : PowerSeries.map φ (ξ g) = ψ g := by
    ext i
    simp [ξ, ψ, φ]
  have hq (i : ℕ) : PowerSeries.coeff i Q =
      (if i = 0 then 1 else 0) - Polynomial.C (PowerSeries.coeff i (2 * a)) * Polynomial.X +
        Polynomial.C (PowerSeries.coeff i (a ^ 2 - d * b ^ 2)) * Polynomial.X ^ 2 := by
    simp only [Q, map_add, map_sub, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_one, ξ, PowerSeries.coeff_map]
  have hq0 : PowerSeries.coeff 0 Q = q := by simp [hq, q]
  have hQ (i : ℕ) : (PowerSeries.coeff i Q).natDegree ≤ 2 := by
    rw [hq]
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] <;> compute_degree
  have hV (i : ℕ) : (PowerSeries.coeff i V).natDegree ≤ 1 := by
    simp only [V, ξ, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_map]
    compute_degree
  have hmapQ : PowerSeries.map φ Q =
      1 - ψ (2 * a) * W + ψ (a ^ 2 - d * b ^ 2) * W ^ 2 := by
    dsimp only [Q]
    rw [map_add (PowerSeries.map φ), map_sub (PowerSeries.map φ), map_one (PowerSeries.map φ),
      map_mul (PowerSeries.map φ), map_mul (PowerSeries.map φ), hm, hm,
      PowerSeries.map_C, PowerSeries.map_C]
    simp only [φ, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_X, map_pow, W]
  have hmapV : PowerSeries.map φ V = ψ f + ψ (f * (-a + y * b)) * W := by
    dsimp only [V]
    rw [map_add, map_mul, hm, hm, PowerSeries.map_C]
    simp only [φ, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, W]
  have hnum : ψ (f * (-a + y * b)) = ψ f * (-ψ a + ψ y * ψ b) := by
    rw [map_mul, map_add, map_neg, map_mul]
  have he : PowerSeries.map φ Q * E = PowerSeries.map φ V := by
    rw [hmapQ, hmapV, hnum]
    dsimp only [E]
    change (1 - ψ (2 * a) * W + ψ (a ^ 2 - d * b ^ 2) * W ^ 2) * K = 1 at hK
    linear_combination (ψ f * (1 - ψ a * W + ψ y * ψ b * W)) * hK
  obtain ⟨P, hdeg, hP⟩ :=
    TranscendenceTheory.formal_series_coefficient_denominator_bound
      R (PowerSeries R) φ Q V E 1 2 he hQ hV k
  rw [hq0] at hP
  change (q : PowerSeries R) ^ (k + 1) * PowerSeries.coeff k E = (P : PowerSeries R) at hP
  have hunit : (q : PowerSeries R) * L = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [q])
  refine ⟨P, by omega, ?_⟩
  change PowerSeries.coeff k E = (P : PowerSeries R) * L ^ (k + 1)
  calc
    _ = ((q : PowerSeries R) * L) ^ (k + 1) * PowerSeries.coeff k E := by
      rw [hunit, one_pow, one_mul]
    _ = ((q : PowerSeries R) ^ (k + 1) * PowerSeries.coeff k E) * L ^ (k + 1) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hP]

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
              ∃ (p : MvPolynomial (Fin 4) ℂ)
                (F : Polynomial (Polynomial ℂ)) (a b s : ℕ),
                F.natDegree ≠ 0 ∧
                (∀ i, (F.coeff i).natDegree ≤ a) ∧
                F.eval₂ (Polynomial.aeval x).toRingHom (Ideal.Quotient.mk I (ρ p)) = 0 ∧
                (∀ z ∈ (F.map φ).roots,
                  ¬ ∃ w : Z × Fin N → L, ∀ i ≤ s, ∀ j ≤ b,
                    (∑ r : Z × Fin N,
                      PowerSeries.coeff i (PowerSeries.coeff r.2.val (E p r.1 j)) • w r) =
                      (φ Polynomial.X) ^ j * z ^ i) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_jet_denominator_obstruction G
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
  intro hnorm τ hτ hdenom
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
  have hrat (p : MvPolynomial (Fin 4) ℂ) (r : Z) (j k : ℕ) :
      ∃ M : Polynomial ℂ, M.natDegree ≤ 2 * k + 1 ∧
        PowerSeries.coeff k (E p r j) = (M : PowerSeries ℂ) * H₀ p r ^ (k + 1) :=
    local_jet_fraction ((J r 1) ^ j) (J r 2) (A p r) (B p r) (D r) (K p r) (hdenom p r) k
  choose M hM using hrat
  obtain ⟨p, F, a, b, s, hFpos, hF, hFx, hroots, hcost⟩ :=
    hbound m n U hm hn hU X hX Q hQ hlocal hdegree hcharts Y hYX hY hcard
      hI P hinit hsecond hcurve ρ hρ hnorm τ hτ hdenom M hM
  refine ⟨p, F, a, b, s, hFpos, hF, hFx, ?_, hcost⟩
  intro z hz hw
  apply hroots z hz
  obtain ⟨w, hw⟩ := hw
  refine ⟨w, ?_⟩
  intro i hi j hj
  change (∑ r : Z × Fin N, PowerSeries.coeff i
    ((M p r.1 j r.2.val : PowerSeries ℂ) * H₀ p r.1 ^ (r.2.val + 1)) • w r) = _
  calc
    _ = ∑ r : Z × Fin N,
        PowerSeries.coeff i (PowerSeries.coeff r.2.val (E p r.1 j)) • w r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [(hM p r.1 j r.2.val).2]
    _ = _ := hw i hi j hj
