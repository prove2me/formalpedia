-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_quadratic_spectrum_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T23:33:08.151987+00:00
-- url     : https://prove2.me/submissions/b780591e-0c27-4ea2-96e9-95ebdf0a8c6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_formal_quadratic_spectrum_factorization
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_chart_spectrum_obstruction
import Theorems.Thm_TranscendenceTheory_affine_coordinate_evaluation
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

private lemma constant_aeval {R σ : Type*} [CommSemiring R]
    (J : σ → PowerSeries R) (p : MvPolynomial σ R) :
    PowerSeries.coeff 0 (MvPolynomial.aeval J p) =
      MvPolynomial.aeval (fun i => PowerSeries.coeff 0 (J i)) p := by
  let ε : PowerSeries R →ₐ[R] R :=
    { PowerSeries.constantCoeff with commutes' := by intro r; simp }
  have he : (ε : PowerSeries R → R) = PowerSeries.constantCoeff := rfl
  rw [PowerSeries.coeff_zero_eq_constantCoeff, ← he]
  exact MvPolynomial.comp_aeval_apply (f := J) ε p

private lemma affine_branch_constants {R σ : Type*} [CommRing R] [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ R) (J : σ → PowerSeries R) (v : σ → R)
    (hp : p.degreeOf i ≤ 1) (hJ : ∀ k, PowerSeries.coeff 0 (J k) = v k) :
    let a := MvPolynomial.aeval (Function.update J i 0) p
    let b := MvPolynomial.aeval (Function.update J i 0) (MvPolynomial.pderiv i p)
    PowerSeries.coeff 0 (a + J i * b) = MvPolynomial.aeval v p ∧
      PowerSeries.coeff 0 (a - J i * b) =
        MvPolynomial.aeval (Function.update v i (-v i)) p := by
  dsimp only
  have hplus := TranscendenceTheory.affine_coordinate_evaluation R (PowerSeries R) σ i p J hp
  have hminus := TranscendenceTheory.affine_coordinate_evaluation R (PowerSeries R) σ i p
    (Function.update J i (-J i)) hp
  simp only [Function.update_self, Function.update_idem, neg_mul, ← sub_eq_add_neg] at hminus
  have hjplus : (fun k => PowerSeries.coeff 0 (J k)) = v := funext hJ
  have hjminus : (fun k => PowerSeries.coeff 0 (Function.update J i (-J i) k)) =
      Function.update v i (-v i) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [Function.update_self, map_neg, hJ]
    · simp [Function.update_of_ne hk, hJ]
  constructor
  · rw [← hplus, constant_aeval, hjplus]
  · rw [← hminus, constant_aeval, hjminus]

private lemma evaluation_mod_cubic {R σ : Type*} [CommRing R]
    (p q c : MvPolynomial σ R) (v : σ → R)
    (h : p - q ∈ Ideal.span ({c} : Set (MvPolynomial σ R)))
    (hc : MvPolynomial.aeval v c = 0) : MvPolynomial.aeval v p = MvPolynomial.aeval v q := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h
  have he := congrArg (MvPolynomial.aeval v) hb
  simp only [map_sub, map_mul, hc, zero_mul] at he
  exact sub_eq_zero.mp he

private lemma chart_spectral_equivalence (S : Type*) [CommRing S] [IsDomain S]
    (f : ℂ →+* S) (g₂ g₃ : ℂ) (v : Fin 4 → ℂ) (P : PowerSeries ℂ)
    (hinit : PowerSeries.coeff 0 P = v 1 ∧ PowerSeries.coeff 1 P = v 2)
    (hcurve : (PowerSeries.derivative ℂ P) ^ 2 =
      PowerSeries.C 4 * P ^ 3 - PowerSeries.C g₂ * P - PowerSeries.C g₃)
    (p q : MvPolynomial (Fin 4) ℂ) (hq : q.degreeOf (2 : Fin 4) ≤ 1)
    (hred : p - q ∈ Ideal.span
      ({WeierstrassEllipticZeta.extensionChartCubic g₂ g₃ 0} : Set (MvPolynomial (Fin 4) ℂ)))
    (z : S) :
    let J : Fin 4 → PowerSeries ℂ :=
      ![PowerSeries.C (v 0) + PowerSeries.X, P, PowerSeries.derivative ℂ P,
        PowerSeries.mk fun k => if k = 0 then v 3 else -PowerSeries.coeff (k - 1) P / (k : ℂ)]
    let D := PowerSeries.C 4 * P ^ 3 - PowerSeries.C g₂ * P - PowerSeries.C g₃
    let A := MvPolynomial.aeval (Function.update J (2 : Fin 4) 0) q
    let B := MvPolynomial.aeval (Function.update J (2 : Fin 4) 0) (MvPolynomial.pderiv 2 q)
    z ^ 2 - f (PowerSeries.coeff 0 (2 * A)) * z +
        f (PowerSeries.coeff 0 (A ^ 2 - D * B ^ 2)) = 0 ↔
      z = f (MvPolynomial.aeval v p) ∨
        z = f (MvPolynomial.aeval (Function.update v (2 : Fin 4) (-v 2)) p) := by
  classical
  let J : Fin 4 → PowerSeries ℂ :=
    ![PowerSeries.C (v 0) + PowerSeries.X, P, PowerSeries.derivative ℂ P,
      PowerSeries.mk fun k => if k = 0 then v 3 else -PowerSeries.coeff (k - 1) P / (k : ℂ)]
  let D := PowerSeries.C 4 * P ^ 3 - PowerSeries.C g₂ * P - PowerSeries.C g₃
  let A := MvPolynomial.aeval (Function.update J (2 : Fin 4) 0) q
  let B := MvPolynomial.aeval (Function.update J (2 : Fin 4) 0) (MvPolynomial.pderiv 2 q)
  dsimp only
  have hJ : ∀ i, PowerSeries.coeff 0 (J i) = v i := by
    intro i
    fin_cases i <;> simp [J, hinit.1, hinit.2, PowerSeries.coeff_derivative]
  have hP0 : PowerSeries.constantCoeff P = v 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hinit.1
  have hY0 : PowerSeries.constantCoeff (PowerSeries.derivative ℂ P) = v 2 := by
    simpa [J] using hJ 2
  have hpoint : v 2 ^ 2 = 4 * v 1 ^ 3 - g₂ * v 1 - g₃ := by
    have ht := congrArg (PowerSeries.constantCoeff : PowerSeries ℂ →+* ℂ) hcurve
    simpa only [map_pow, map_sub, map_mul, PowerSeries.constantCoeff_C, hP0, hY0] using ht
  have hc : MvPolynomial.aeval v (WeierstrassEllipticZeta.extensionChartCubic g₂ g₃ 0) = 0 := by
    simp only [WeierstrassEllipticZeta.extensionChartCubic, ↓reduceIte,
      map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [hpoint]
    ring
  have hc' : MvPolynomial.aeval (Function.update v (2 : Fin 4) (-v 2))
      (WeierstrassEllipticZeta.extensionChartCubic g₂ g₃ 0) = 0 := by
    simpa [WeierstrassEllipticZeta.extensionChartCubic] using hc
  have hbranches := affine_branch_constants (2 : Fin 4) q J v hq hJ
  have hplus : PowerSeries.coeff 0 (A + PowerSeries.derivative ℂ P * B) =
      MvPolynomial.aeval v p :=
    hbranches.1.trans (evaluation_mod_cubic p q _ v hred hc).symm
  have hminus : PowerSeries.coeff 0 (A - PowerSeries.derivative ℂ P * B) =
      MvPolynomial.aeval (Function.update v (2 : Fin 4) (-v 2)) p :=
    hbranches.2.trans (evaluation_mod_cubic p q _ _ hred hc').symm
  simpa only [hplus, hminus] using
    TranscendenceTheory.formal_quadratic_spectrum_factorization ℂ S f A B D
      (PowerSeries.derivative ℂ P) hcurve z

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
                    z ^ 2 - algebraMap ℂ L (PowerSeries.coeff 0 (2 * A p r)) * z +
                      algebraMap ℂ L
                        (PowerSeries.coeff 0 (A p r ^ 2 - D r * B p r ^ 2)) = 0) →
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
    WeierstrassEllipticZeta.bounded_subset_chart_spectrum_obstruction G
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
  have hiff (r : Z) (z : L) :
      z ^ 2 - algebraMap ℂ L (PowerSeries.coeff 0 (2 * A p r)) * z +
          algebraMap ℂ L (PowerSeries.coeff 0 (A p r ^ 2 - D r * B p r ^ 2)) = 0 ↔
        z = algebraMap ℂ L (MvPolynomial.aeval (v r) p) ∨
          z = algebraMap ℂ L
            (MvPolynomial.aeval (Function.update (v r) (2 : Fin 4) (-v r 2)) p) :=
    chart_spectral_equivalence L (algebraMap ℂ L) G.L.g₂ G.L.g₃ (v r) (P r)
      (hinit r) (hcurve r) p (ρ p) (hρ p).1 (hρ p).2 z
  refine ⟨p, F, a, b, s, hFpos, hF, hFx, ?_, hcost⟩
  intro z hz hcondition hweights
  apply hroots z hz ?_ hweights
  rcases hcondition with hs | ⟨r, hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨r, (hiff r z).mp hr⟩
