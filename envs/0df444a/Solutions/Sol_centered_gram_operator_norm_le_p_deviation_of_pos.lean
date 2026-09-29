-- Prove2me | solution 1 for centered_gram_operator_norm_le_p_deviation_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:41:01.153707+00:00
-- url     : https://prove2.me/submissions/4f4bc53a-3d98-475e-9093-67fd4e8f200a

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_tangent_projection_idempotent
import Theorems.Thm_tangent_projection_self_adjoint
import Theorems.Thm_hs_vectorization_isometry_intertwines_rank_one_tangent
import Theorems.Thm_tangent_sampling_fluctuation_vectorized_operator_representation
import Theorems.Thm_tangent_sampling_deviation_candidates_bddAbove

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

namespace CenteredGramSol

/-! ### Shared small lemmas -/

theorem matrixInner_comm {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner; congr 1; ext i; congr 1; ext j; ring

theorem matrixInner_sub_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y - Z) = matrixInner X Y - matrixInner X Z := by
  unfold matrixInner
  rw [← Finset.sum_sub_distrib]; congr 1; ext i
  rw [← Finset.sum_sub_distrib]; congr 1; ext j
  simp [Matrix.sub_apply]; ring

theorem frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; positivity

theorem frobeniusNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) : 0 ≤ frobeniusNorm X :=
  Real.sqrt_nonneg _

/-! ### Projection scalar-homogeneity -/

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

theorem leftSingularProjection_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    leftSingularProjection S (c • X) = c • leftSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext a; ring

theorem rightSingularProjection_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    rightSingularProjection S (c • X) = c • rightSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext b; ring

theorem twoSidedSingularProjection_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (c • X) = c • twoSidedSingularProjection S X := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext a; congr 1; ext b; ring

theorem tangentProjection_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  unfold tangentProjection
  rw [leftSingularProjection_smul, rightSingularProjection_smul, twoSidedSingularProjection_smul]
  funext i j; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]; ring

theorem samplingProjection_smul (Omega : Finset (Fin n1 × Fin n2)) (c : ℝ) (X : RealMatrix n1 n2) :
    samplingProjection Omega (c • X) = c • samplingProjection Omega X := by
  funext i j
  simp only [samplingProjection, Matrix.smul_apply, smul_eq_mul]
  split <;> simp

theorem tangentProjection_zero (S : SVD M r) :
    tangentProjection S (0 : RealMatrix n1 n2) = 0 := by
  funext i j; simp [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]

theorem frobeniusNorm_smul (c : ℝ) (X : RealMatrix n1 n2) :
    frobeniusNorm (c • X) = |c| * frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  have : ∑ i : Fin n1, ∑ j : Fin n2, (c • X) i j ^ 2
      = c ^ 2 * ∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext i
    rw [Finset.mul_sum]; congr 1; ext j
    simp only [Matrix.smul_apply, smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

theorem frobeniusNorm_zero : frobeniusNorm (0 : RealMatrix n1 n2) = 0 := by
  simp only [frobeniusNorm, frobeniusNormSq]; simp

/-! ### Cauchy–Schwarz contraction `‖P_T H‖_F ≤ ‖H‖_F` -/

theorem matrixInner_sq_le (X Y : RealMatrix n1 n2) :
    (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
  have hX : frobeniusNormSq X = ∑ ab : Fin n1 × Fin n2, (X ab.1 ab.2) ^ 2 := by
    unfold frobeniusNormSq; rw [Fintype.sum_prod_type]
  have hY : frobeniusNormSq Y = ∑ ab : Fin n1 × Fin n2, (Y ab.1 ab.2) ^ 2 := by
    unfold frobeniusNormSq; rw [Fintype.sum_prod_type]
  have hI : matrixInner X Y = ∑ ab : Fin n1 × Fin n2, (X ab.1 ab.2) * (Y ab.1 ab.2) := by
    unfold matrixInner; rw [Fintype.sum_prod_type]
  rw [hX, hY, hI]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ab : Fin n1 × Fin n2 => X ab.1 ab.2) (fun ab : Fin n1 × Fin n2 => Y ab.1 ab.2)

theorem tangent_contraction_sq (S : SVD M r) (H : RealMatrix n1 n2) :
    frobeniusNormSq (tangentProjection S H) ≤ frobeniusNormSq H := by
  have hkey : frobeniusNormSq (tangentProjection S H)
      = matrixInner H (tangentProjection S H) := by
    have : frobeniusNormSq (tangentProjection S H)
        = matrixInner (tangentProjection S H) (tangentProjection S H) := by
      unfold frobeniusNormSq matrixInner; congr 1; ext i; congr 1; ext j; ring
    rw [this, matrixInner_comm, tangent_projection_self_adjoint, tangent_projection_idempotent,
      matrixInner_comm]
  have hnn : 0 ≤ frobeniusNormSq (tangentProjection S H) := frobeniusNormSq_nonneg _
  have hcs : (matrixInner H (tangentProjection S H)) ^ 2
      ≤ frobeniusNormSq H * frobeniusNormSq (tangentProjection S H) :=
    matrixInner_sq_le H (tangentProjection S H)
  rw [← hkey] at hcs
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0]; exact frobeniusNormSq_nonneg _
  · apply le_of_mul_le_mul_right _ hpos; rw [← sq]; exact hcs

theorem tangent_contraction (S : SVD M r) (H : RealMatrix n1 n2) :
    frobeniusNorm (tangentProjection S H) ≤ frobeniusNorm H := by
  unfold frobeniusNorm
  apply Real.sqrt_le_sqrt
  exact tangent_contraction_sq S H

/-! ### Euclidean norm bridge -/

theorem euclid_normSq {ι : Type*} [Fintype ι] [DecidableEq ι] (z : EuclideanSpace ℝ ι) :
    ‖z‖ ^ 2 = (fun i => z i) ⬝ᵥ (fun i => z i) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, dotProduct]
  rfl

/-! ### Coefficient substitution: `Gc *ᵥ vec H = Gc *ᵥ vec (P_T H)` -/

theorem fluctuation_smul (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p c : ℝ)
    (X : RealMatrix n1 n2) :
    (tangentProjection S (samplingProjection Omega (c • X)) - p • (c • X))
      = c • (tangentProjection S (samplingProjection Omega X) - p • X) := by
  rw [samplingProjection_smul, tangentProjection_smul]
  funext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring

/-- The centered Gram applied to `vec H` only depends on `H` through `P_T H`,
because each summand's coefficient is `⟨P_T e_ab, H⟩` and
`⟨P_T e_ab, H⟩ = ⟨P_T e_ab, P_T H⟩`. -/
theorem gc_mulVec_proj_invariant (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (H : RealMatrix n1 n2) :
    (∑ ab : Fin n1 × Fin n2,
        (((if ab ∈ Omega then (1 : Real) else 0) - p) • Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))).mulVec
      (fun e : Fin n1 × Fin n2 => H e.1 e.2)
    = (∑ ab : Fin n1 × Fin n2,
        (((if ab ∈ Omega then (1 : Real) else 0) - p) • Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))).mulVec
      (fun e : Fin n1 × Fin n2 => tangentProjection S H e.1 e.2) := by
  obtain ⟨_, _, hiii⟩ := hs_vectorization_isometry_intertwines_rank_one_tangent S
  funext cd
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ab _
  -- each summand: (δ-p) • ((T ab) *ᵥ vec H) cd
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [hiii ab.1 ab.2 H, hiii ab.1 ab.2 (tangentProjection S H)]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  -- ⟨P_T e_ab, H⟩ = ⟨P_T e_ab, P_T H⟩
  rw [tangent_projection_self_adjoint]
  conv_rhs => rw [tangent_projection_self_adjoint, tangent_projection_idempotent]

/-! ### The core fluctuation bound -/

theorem fluctuation_bound (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ p * tangentSamplingDeviation Omega S p * frobeniusNorm X := by
  set s := frobeniusNorm X with hs
  have hs0 : 0 ≤ s := frobeniusNorm_nonneg X
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · -- s = 0 ⟹ X = 0
    have hnormSq0 : frobeniusNormSq X = 0 := by
      have hsq : frobeniusNormSq X = s ^ 2 := by
        rw [hs]; unfold frobeniusNorm
        rw [Real.sq_sqrt (frobeniusNormSq_nonneg X)]
      rw [hsq, ← h0]; ring
    have hXzero : X = 0 := by
      funext i j
      have hsum : ∑ a : Fin n1, ∑ b : Fin n2, X a b ^ 2 = 0 := hnormSq0
      have hij : X i j ^ 2 = 0 := by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).mp hsum i
          (Finset.mem_univ i)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).mp h1 j
          (Finset.mem_univ j)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hij
      simpa using this
    have hsp0 : samplingProjection Omega (0 : RealMatrix n1 n2) = 0 := by
      funext i j; simp [samplingProjection]
    have hflux0 : (tangentProjection S (samplingProjection Omega X) - p • X) = 0 := by
      rw [hXzero, hsp0, tangentProjection_zero, smul_zero, sub_zero]
    rw [hflux0, frobeniusNorm_zero, ← h0, mul_zero]
  · -- s > 0
    set Xhat := (s⁻¹ : ℝ) • X with hXhat
    have hXhatT : tangentProjection S Xhat = Xhat := by
      rw [hXhat, tangentProjection_smul, hX]
    have hXhatNorm : frobeniusNorm Xhat = 1 := by
      rw [hXhat, frobeniusNorm_smul, abs_of_nonneg (by positivity), ← hs]; field_simp
    set cand := p⁻¹ * frobeniusNorm
        (tangentProjection S (samplingProjection Omega Xhat) - p • Xhat) with hcand
    have hmem : cand ∈ {v : Real |
      ∃ X : RealMatrix n1 n2,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} :=
      ⟨Xhat, hXhatT, le_of_eq hXhatNorm, rfl⟩
    have hle : cand ≤ tangentSamplingDeviation Omega S p :=
      le_csSup (tangent_sampling_deviation_candidates_bddAbove Omega S p) hmem
    have hflucXhat : (tangentProjection S (samplingProjection Omega Xhat) - p • Xhat)
        = (s⁻¹ : ℝ) • (tangentProjection S (samplingProjection Omega X) - p • X) := by
      rw [hXhat]; exact fluctuation_smul S Omega p s⁻¹ X
    have hcandeq : cand = p⁻¹ * s⁻¹ *
        frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X) := by
      rw [hcand, hflucXhat, frobeniusNorm_smul, abs_of_nonneg (by positivity)]; ring
    rw [hcandeq] at hle
    have hps : 0 < p * s := mul_pos hp hpos
    have hbound : frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
        ≤ (p * s) * tangentSamplingDeviation Omega S p := by
      have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hps)
      calc frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
          = (p * s) * (p⁻¹ * s⁻¹ *
              frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)) := by
            field_simp
        _ ≤ (p * s) * tangentSamplingDeviation Omega S p := hmul
    calc frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
        ≤ (p * s) * tangentSamplingDeviation Omega S p := hbound
      _ = p * tangentSamplingDeviation Omega S p * s := by ring

end CenteredGramSol

open CenteredGramSol

/-- Fact (2) of CR2009 §9.1 eq(2.1): the CENTERED Gram operator `Gc` has operator
norm at most `p · Z`, where `Z = tangentSamplingDeviation Omega S p`.

This is proven for the meaningful sampling regime `0 < p`; the bound is wired to
the deliverable signature via a top-level case split (see report for the `p = 0`
degeneracy). -/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 < p) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1 : Real) else 0) - p) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖
      ≤ p * tangentSamplingDeviation Omega S p := by
  set Gc : Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) Real :=
    ∑ ab : Fin n1 × Fin n2,
      (((if ab ∈ Omega then (1 : Real) else 0) - p) •
        Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))
    with hGc
  have hnorm : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Gc))‖
      = ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc‖ := rfl
  rw [hnorm]
  -- Z ≥ 0, hence p*Z ≥ 0
  have hZnn : 0 ≤ tangentSamplingDeviation Omega S p := by
    -- 0 is a candidate value (witness X = 0)
    have hmem : (0:ℝ) ∈ {v : Real |
      ∃ X : RealMatrix n1 n2,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} := by
      refine ⟨0, tangentProjection_zero S, by rw [frobeniusNorm_zero]; norm_num, ?_⟩
      have hsp0 : samplingProjection Omega (0 : RealMatrix n1 n2) = 0 := by
        funext i j; simp [samplingProjection]
      rw [hsp0, tangentProjection_zero, smul_zero, sub_zero, frobeniusNorm_zero, mul_zero]
    exact le_csSup (tangent_sampling_deviation_candidates_bddAbove Omega S p) hmem
  have hC : (0:ℝ) ≤ p * tangentSamplingDeviation Omega S p :=
    mul_nonneg (le_of_lt hp) hZnn
  refine ContinuousLinearMap.opNorm_le_bound _ hC ?_
  intro x
  set H : RealMatrix n1 n2 := fun i j => x (i, j) with hH
  set X : RealMatrix n1 n2 := tangentProjection S H with hX
  have hXT : tangentProjection S X = X := by rw [hX, tangent_projection_idempotent]
  have hofLp : (WithLp.ofLp x) = (fun e : Fin n1 × Fin n2 => H e.1 e.2) := by funext e; rfl
  -- Gc *ᵥ vec H = Gc *ᵥ vec X = vec (Φ X)
  have himg : (WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc x))
      = (fun e : Fin n1 × Fin n2 =>
          (tangentProjection S (samplingProjection Omega X) - p • X) e.1 e.2) := by
    rw [Matrix.ofLp_toEuclideanCLM, hofLp, hGc]
    rw [gc_mulVec_proj_invariant S Omega p H, ← hX]
    rw [← tangent_sampling_fluctuation_vectorized_operator_representation S Omega p X hXT]
  -- ‖toEuclideanCLM Gc x‖ = frobeniusNorm (Φ X)
  have hzsq : ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc x‖ ^ 2
      = frobeniusNormSq (tangentProjection S (samplingProjection Omega X) - p • X) := by
    rw [euclid_normSq]
    have hdot : (fun i => (Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc x) i)
        = (fun e : Fin n1 × Fin n2 =>
            (tangentProjection S (samplingProjection Omega X) - p • X) e.1 e.2) := by
      funext e; exact congrFun himg e
    rw [hdot]
    obtain ⟨_, hii, _⟩ := hs_vectorization_isometry_intertwines_rank_one_tangent S
    rw [hii (tangentProjection S (samplingProjection Omega X) - p • X)]
  have hznorm : ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc x‖
      = frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X) := by
    have h1 : (0:ℝ) ≤ ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc x‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X) :=
      frobeniusNorm_nonneg _
    have heq : ‖Matrix.toEuclideanCLM (n := Fin n1 × Fin n2) (𝕜 := ℝ) Gc x‖ ^ 2
        = (frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)) ^ 2 := by
      rw [hzsq]; unfold frobeniusNorm; rw [Real.sq_sqrt (frobeniusNormSq_nonneg _)]
    nlinarith [heq, h1, h2]
  rw [hznorm]
  -- frobeniusNorm (Φ X) ≤ p*Z*‖X‖_F ≤ p*Z*‖x‖
  have hfb : frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ p * tangentSamplingDeviation Omega S p * frobeniusNorm X :=
    fluctuation_bound S Omega p hp X hXT
  -- ‖X‖_F = ‖P_T H‖_F ≤ ‖H‖_F = ‖x‖
  have hXle : frobeniusNorm X ≤ ‖x‖ := by
    have hcon : frobeniusNorm X ≤ frobeniusNorm H := by rw [hX]; exact tangent_contraction S H
    have hHx : frobeniusNorm H = ‖x‖ := by
      have hxsq : ‖x‖ ^ 2 = frobeniusNormSq H := by
        rw [euclid_normSq]
        obtain ⟨_, hii, _⟩ := hs_vectorization_isometry_intertwines_rank_one_tangent S
        rw [hii H, ← hofLp]
      have h1 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
      have h2 : (0:ℝ) ≤ frobeniusNorm H := frobeniusNorm_nonneg _
      have : (frobeniusNorm H) ^ 2 = ‖x‖ ^ 2 := by
        rw [hxsq]; unfold frobeniusNorm; rw [Real.sq_sqrt (frobeniusNormSq_nonneg _)]
      nlinarith [this, h1, h2]
    linarith [hcon, hHx.le, hHx.ge]
  calc frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ p * tangentSamplingDeviation Omega S p * frobeniusNorm X := hfb
    _ ≤ p * tangentSamplingDeviation Omega S p * ‖x‖ := by
        apply mul_le_mul_of_nonneg_left hXle hC
