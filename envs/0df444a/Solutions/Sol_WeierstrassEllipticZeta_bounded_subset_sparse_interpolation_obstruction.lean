-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_subset_sparse_interpolation_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-19T18:28:41.444381+00:00
-- url     : https://prove2.me/submissions/3877657a-c146-479d-8470-ba08f89fcb00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TranscendenceTheory_sparse_inconsistency_certificate
import Theorems.Thm_TranscendenceTheory_bounded_polynomial_family_rank_obstruction
import Theorems.Thm_WeierstrassEllipticZeta_bounded_subset_finite_rank_obstruction
import Mathlib.Data.Matrix.ColumnRowPartitioned
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



private theorem finite_family_rank_obstruction
    (K α ι κ : Type*) [Field K] [Fintype α] [Fintype ι] [Fintype κ]
    (A : Matrix α ι K) (B : Matrix α κ K) :
    (∃ k, ¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a k) ↔
      A.rank < (Matrix.fromCols A B).rank := by
  classical
  let S := Submodule.span K (Set.range A.col)
  let T := Submodule.span K (Set.range (Matrix.fromCols A B).col)
  have hST : S ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hB (k : κ) : B.col k ∈ S ↔
      ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a k := by
    rw [Submodule.mem_span_range_iff_exists_fun K]
    apply exists_congr
    intro u
    rw [funext_iff]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, mul_comm]
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  change (∃ k, ¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a k) ↔
    Module.finrank K S < Module.finrank K T
  constructor
  · rintro ⟨k, hk⟩
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne hST ?_
    intro heq
    apply hk
    apply (hB k).mp
    rw [heq]
    exact Submodule.subset_span ⟨Sum.inr k, rfl⟩
  · intro hrank
    by_contra hnone
    have hTS : T ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i | k, rfl⟩
      · exact Submodule.subset_span ⟨i, rfl⟩
      · apply (hB k).mpr
        by_contra hk
        exact hnone ⟨k, hk⟩
    exact (not_lt_of_ge (Submodule.finrank_mono hTS)) hrank

private lemma weighted_poly_coeff
    {K ι : Type*} [CommRing K] [Fintype ι]
    (P : Polynomial K) (V : ι → Polynomial K) (u : ι → K) (n : ℕ) :
    (P * ∑ i, Polynomial.C (u i) * V i).coeff n =
      ∑ i, (P * V i).coeff n * u i := by
  classical
  rw [Finset.mul_sum]
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show P * (Polynomial.C (u i) * V i) = Polynomial.C (u i) * (P * V i) by ring]
  rw [Polynomial.coeff_C_mul]
  exact mul_comm _ _

private lemma exact_poly_system_iff
    (K ι : Type*) [Field K] [Fintype ι]
    (b : ℕ) (P : Polynomial K) (V : ι → ℕ → Polynomial K) (Q : ℕ → Polynomial K) :
    (∃ u : ι → K, ∀ j ≤ b, P * (∑ i, Polynomial.C (u i) * V i j) = Q j) ↔
    (∃ u : ι → K, ∀ e : Fin (b + 1) × ℕ,
      ∑ i, (P * V i e.1.val).coeff e.2 * u i = (Q e.1.val).coeff e.2) := by
  classical
  apply exists_congr
  intro u
  constructor
  · intro hu e
    have h := congrArg (fun p : Polynomial K => p.coeff e.2) (hu e.1.val (by omega))
    simpa only [weighted_poly_coeff] using h
  · intro hu j hj
    ext n
    simpa only [weighted_poly_coeff] using hu (⟨j, by omega⟩, n)


private lemma sparse_exact_poly_obstruction
    (K ι : Type*) [Field K] [Fintype ι]
    (b : ℕ) (P : Polynomial K) (V : ι → ℕ → Polynomial K) (Q : ℕ → Polynomial K) :
    (¬ ∃ u : ι → K, ∀ j ≤ b, P * (∑ i, Polynomial.C (u i) * V i j) = Q j) ↔
    ∃ r : ℕ, r ≤ Fintype.card ι + 1 ∧
      ∃ e : Fin r → Fin (b + 1) × ℕ, ∃ μ : Fin r → K,
        (∀ i, ∑ t, μ t * (P * V i (e t).1.val).coeff (e t).2 = 0) ∧
        ∑ t, μ t * (Q (e t).1.val).coeff (e t).2 = 1 := by
  exact (not_congr (exact_poly_system_iff K ι b P V Q)).trans
    (TranscendenceTheory.sparse_inconsistency_certificate K ι (Fin (b + 1) × ℕ)
      (fun e i => (P * V i e.1.val).coeff e.2) (fun e => (Q e.1.val).coeff e.2))

private lemma finite_sparse_rank
    (K α ι : Type*) [Field K] [Fintype α] [Fintype ι]
    (A : Matrix α ι K) (B : α → K) :
    (∃ r : ℕ, r ≤ Fintype.card ι + 1 ∧
      ∃ e : Fin r → α, ∃ μ : Fin r → K,
        (∀ i, ∑ t, μ t * A (e t) i = 0) ∧
        ∑ t, μ t * B (e t) = 1) ↔
      A.rank < (Matrix.fromCols A (fun a (_ : Unit) => B a)).rank := by
  have hsingle :
      (¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a) ↔
      (∃ _ : Unit, ¬ ∃ u : ι → K, ∀ a, ∑ i, A a i * u i = B a) := by
    exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  exact (TranscendenceTheory.sparse_inconsistency_certificate K ι α A B).symm.trans
    (hsingle.trans (finite_family_rank_obstruction K α ι Unit A (fun a _ => B a)))

private lemma bounded_exact_poly_family_rank
    (K ι : Type*) [Field K] [Fintype ι]
    (b d : ℕ) (c : K) (V : ι → ℕ → Polynomial K) (Q : Polynomial K)
    (hV : ∀ i j, (V i j).natDegree < d) (hQ : Q.natDegree ≤ d) :
    (∃ k ≤ b, ¬ ∃ u : ι → K, ∀ j ≤ b,
      (1 - Polynomial.C c * Polynomial.X) *
        (∑ i, Polynomial.C (u i) * V i j) = if k = j then Q else 0) ↔
      let Ac : Matrix (Fin (b + 1) × Fin (d + 1)) ι K := fun e i =>
        ((1 - Polynomial.C c * Polynomial.X) * V i e.1.val).coeff e.2.val
      let Bc : Matrix (Fin (b + 1) × Fin (d + 1)) (Fin (b + 1)) K := fun e k =>
        (if k.val = e.1.val then Q else 0).coeff e.2.val
      Ac.rank < (Matrix.fromCols Ac Bc).rank := by
  classical
  let P : Polynomial K := 1 - Polynomial.C c * Polynomial.X
  let A : Fin (b + 1) → ι → Polynomial K := fun j i => P * V i j.val
  let B : Fin (b + 1) → Fin (b + 1) → Polynomial K := fun j k =>
    if k.val = j.val then Q else 0
  have hP : P.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le 1 (Polynomial.C c * Polynomial.X)).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le c Polynomial.X).trans (by simp)
  have hA (j : Fin (b + 1)) (i : ι) : (A j i).natDegree ≤ d := by
    have hm := Polynomial.natDegree_mul_le (p := P) (q := V i j.val)
    have hv := hV i j.val
    change (P * V i j.val).natDegree ≤ d
    omega
  have hB (j k : Fin (b + 1)) : (B j k).natDegree ≤ d := by
    dsimp [B]
    split_ifs <;> simp_all
  have hsum (u : ι → K) (j : ℕ) :
      (∑ i, Polynomial.C (u i) * (P * V i j)) =
        P * (∑ i, Polynomial.C (u i) * V i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsys (k : Fin (b + 1)) :
      (∃ u : ι → K, ∀ j : Fin (b + 1), ∑ i, Polynomial.C (u i) * A j i = B j k) ↔
      (∃ u : ι → K, ∀ j ≤ b, P * (∑ i, Polynomial.C (u i) * V i j) =
        if k.val = j then Q else 0) := by
    apply exists_congr
    intro u
    constructor
    · intro hu j hj
      simpa only [A, B, hsum] using hu ⟨j, by omega⟩
    · intro hu j
      simpa only [A, B, hsum] using hu j.val (by omega)
  have hind :
      (∃ k ≤ b, ¬ ∃ u : ι → K, ∀ j ≤ b,
        P * (∑ i, Polynomial.C (u i) * V i j) = if k = j then Q else 0) ↔
      (∃ k : Fin (b + 1), ¬ ∃ u : ι → K, ∀ j : Fin (b + 1),
        ∑ i, Polynomial.C (u i) * A j i = B j k) := by
    constructor
    · rintro ⟨k, hk, hno⟩
      exact ⟨⟨k, by omega⟩, (not_congr (hsys ⟨k, by omega⟩)).mpr hno⟩
    · rintro ⟨k, hno⟩
      exact ⟨k.val, by omega, (not_congr (hsys k)).mp hno⟩
  exact hind.trans (TranscendenceTheory.bounded_polynomial_family_rank_obstruction
    K (Fin (b + 1)) ι (Fin (b + 1)) d A B hA hB)

set_option maxHeartbeats 600000 in
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
                  if s < 2 * N * Z.card then
                    ∃ r : ℕ, r ≤ Fintype.card (Z × Fin N) + 1 ∧
                      ∃ e : Fin r → Fin (b + 1) × Fin (s + 1), ∃ μ : Fin r → L,
                        (∀ q : Z × Fin N, ∑ t, μ t *
                          ((1 - Polynomial.C z * Polynomial.X) *
                            (V p q.1 (e t).1.val q.2).map (algebraMap ℂ L)).coeff
                              (e t).2.val = 0) ∧
                        ∑ t, μ t *
                          (Polynomial.C ((φ Polynomial.X) ^ (e t).1.val) *
                            (Ω p).map (algebraMap ℂ L)).coeff (e t).2.val = 1
                  else
                    ∀ c : ℂ, z = algebraMap ℂ L c →
                      ∃ k ≤ b, ∃ r : ℕ, r ≤ Fintype.card (Z × Fin N) + 1 ∧
                        ∃ e : Fin r → Fin (b + 1) × ℕ, ∃ μ : Fin r → ℂ,
                          (∀ q : Z × Fin N, ∑ t, μ t *
                            ((1 - Polynomial.C c * Polynomial.X) *
                              V p q.1 (e t).1.val q.2).coeff (e t).2 = 0) ∧
                          ∑ t, μ t *
                            (if k = (e t).1.val then Ω p else 0).coeff (e t).2 = 1) ∧
                ((2 * (F.natDegree * b + s * a) + ((U : ℕ) + 1) : ℕ) : ℝ) ≤
                  C * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    WeierstrassEllipticZeta.bounded_subset_finite_rank_obstruction G
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
  refine ⟨p, F, a, b, s, hFpos, hF, hFx, ?_, hcost⟩
  intro z hz hguard
  have ht := hroots z hz hguard
  by_cases hs : s < 2 * (3 * (U : ℕ) + 1) * (Y.filter (fun z => z ∉ G.L.lattice)).card
  · simp only [if_pos hs] at ht ⊢
    have hcert := (finite_sparse_rank L (Fin (b + 1) × Fin (s + 1))
      (Z × Fin N) _ _).mpr ht
    exact hcert
  · simp only [if_neg hs] at ht ⊢
    intro c hc
    have hdegV : ∀ (q : Z × Fin N) (j : ℕ),
        (V p q.1 j q.2).natDegree < 2 * N * Z.card :=
      fun q j => (hV p q.1 j q.2).1
    have hdegQ : (Ω p).natDegree ≤ 2 * N * Z.card := (hΩ p).1
    obtain ⟨k, hk, hno⟩ := (bounded_exact_poly_family_rank ℂ (Z × Fin N)
      b (2 * N * Z.card) c (fun q j => V p q.1 j q.2) (Ω p) hdegV hdegQ).mpr (ht c hc)
    refine ⟨k, hk, ?_⟩
    exact (sparse_exact_poly_obstruction ℂ (Z × Fin N) b
      (1 - Polynomial.C c * Polynomial.X) (fun q j => V p q.1 j q.2)
      (fun j => if k = j then Ω p else 0)).mp hno
