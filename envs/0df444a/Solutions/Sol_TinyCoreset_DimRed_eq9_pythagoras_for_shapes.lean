-- Prove2me | solution 1 for TinyCoreset.DimRed.eq9_pythagoras_for_shapes
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:29:09.945772+00:00
-- url     : https://prove2.me/submissions/74759bb8-17b9-493d-8bf8-0b0ef7599b94

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting
set_option autoImplicit false
open scoped Matrix
open TinyCoreset.DimRed

lemma tcd9_proj_sum {d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0) :
    X * Xᵀ + Y * Yᵀ = 1 := by
  have hYX : Yᵀ * X = 0 := by
    have := congrArg Matrix.transpose hXY
    simpa [Matrix.transpose_mul] using this
  have e : Fin d ≃ Fin j ⊕ Fin (d - j) :=
    (finCongr (by omega : d = j + (d - j))).trans finSumFinEquiv.symm
  have hM : Matrix.fromRows Xᵀ Yᵀ * Matrix.fromCols X Y = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hX, hY, hXY, hYX, Matrix.fromBlocks_one]
  have h2 := (Matrix.fromCols_mul_fromRows_eq_one_comm e X Y Xᵀ Yᵀ).2 hM
  rwa [Matrix.fromCols_mul_fromRows] at h2

/-- pointwise Pythagoras for one row -/
lemma tcd9_row {d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0)
    (b : Fin d → ℝ) (z : Fin j → ℝ) :
    ((b - X *ᵥ z) ⬝ᵥ (b - X *ᵥ z)) =
      ((b ᵥ* Y) ⬝ᵥ (b ᵥ* Y)) +
        ((b ᵥ* (X * Xᵀ) - X *ᵥ z) ⬝ᵥ (b ᵥ* (X * Xᵀ) - X *ᵥ z)) := by
  have hYX : Yᵀ * X = 0 := by
    have := congrArg Matrix.transpose hXY
    simpa [Matrix.transpose_mul] using this
  have hsum := tcd9_proj_sum hjd X Y hX hY hXY
  set a : Fin (d - j) → ℝ := b ᵥ* Y with ha
  set w : Fin d → ℝ := Y *ᵥ a with hw
  have hw' : w = b ᵥ* (Y * Yᵀ) := by
    rw [hw, ← Matrix.vecMul_transpose, ha, Matrix.vecMul_vecMul]
  have hp' : b ᵥ* (X * Xᵀ) = X *ᵥ (b ᵥ* X) := by
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul]
  have hb : b = b ᵥ* (X * Xᵀ) + w := by
    rw [hw', ← Matrix.vecMul_add, hsum, Matrix.vecMul_one]
  have hwX : w ᵥ* X = 0 := by
    rw [hw, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hYX, Matrix.vecMul_zero]
  have hww : w ⬝ᵥ w = a ⬝ᵥ a := by
    have : w ᵥ* Y = a := by
      rw [hw, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hY, Matrix.vecMul_one]
    calc w ⬝ᵥ w = w ⬝ᵥ (Y *ᵥ a) := by rw [← hw]
      _ = (w ᵥ* Y) ⬝ᵥ a := by rw [Matrix.dotProduct_mulVec]
      _ = a ⬝ᵥ a := by rw [this]
  have horth : w ⬝ᵥ (b ᵥ* (X * Xᵀ) - X *ᵥ z) = 0 := by
    rw [hp', ← Matrix.mulVec_sub, Matrix.dotProduct_mulVec, hwX, zero_dotProduct]
  have hdec : b - X *ᵥ z = w + (b ᵥ* (X * Xᵀ) - X *ᵥ z) := by
    nth_rewrite 1 [hb]; abel
  rw [hdec, add_dotProduct, dotProduct_add, dotProduct_add, hww, horth, dotProduct_comm _ w, horth]
  ring

lemma tcd9_dist_sq {d : ℕ} (u v : Fin d → ℝ) :
    dist (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 v) ^ 2 = (u - v) ⬝ᵥ (u - v) := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
  simp [dotProduct, sq, Real.dist_eq, abs_mul_abs_self]

lemma tcd9_inf {d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty)
    (hCX : C ⊆ LinearMap.range (Matrix.toEuclideanLin X)) (b : Fin d → ℝ) :
    Metric.infDist (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)) C ^ 2 =
      (b ᵥ* Y) ⬝ᵥ (b ᵥ* Y) +
        Metric.infDist (WithLp.toLp 2 (b ᵥ* (X * Xᵀ)) : EuclideanSpace ℝ (Fin d)) C ^ 2 := by
  set K : ℝ := (b ᵥ* Y) ⬝ᵥ (b ᵥ* Y) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
  set pp : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (b ᵥ* (X * Xᵀ)) with hpp
  set bb : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 b with hbb
  have hdist : ∀ c ∈ C, dist bb c ^ 2 = K + dist pp c ^ 2 := by
    intro c hc
    obtain ⟨z, hz⟩ := hCX hc
    have hcz : c = WithLp.toLp 2 (X *ᵥ z.ofLp) := by
      rw [← hz]; simp [Matrix.toEuclideanLin_apply]
    rw [hcz, hbb, hpp, tcd9_dist_sq, tcd9_dist_sq]
    exact tcd9_row hjd X Y hX hY hXY b z.ofLp
  set I := Metric.infDist bb C with hI
  set D := Metric.infDist pp C with hD
  have hI0 : 0 ≤ I := Metric.infDist_nonneg
  have hD0 : 0 ≤ D := Metric.infDist_nonneg
  have h1 : K + D ^ 2 ≤ I ^ 2 := by
    have : Real.sqrt (K + D ^ 2) ≤ I := by
      rw [hI, Metric.le_infDist hC]
      intro c hc
      have h2 : D ≤ dist pp c := Metric.infDist_le_dist_of_mem hc
      have h3 : K + D ^ 2 ≤ dist bb c ^ 2 := by
        rw [hdist c hc]; nlinarith
      calc Real.sqrt (K + D ^ 2) ≤ Real.sqrt (dist bb c ^ 2) := Real.sqrt_le_sqrt h3
        _ = dist bb c := Real.sqrt_sq dist_nonneg
    have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    rwa [Real.sq_sqrt (by positivity)] at h4
  have h2 : I ^ 2 ≤ K + D ^ 2 := by
    have : Real.sqrt (max 0 (I ^ 2 - K)) ≤ D := by
      rw [hD, Metric.le_infDist hC]
      intro c hc
      have h5 : I ≤ dist bb c := Metric.infDist_le_dist_of_mem hc
      have h6 : I ^ 2 ≤ dist bb c ^ 2 := pow_le_pow_left₀ hI0 h5 2
      have h7 : max 0 (I ^ 2 - K) ≤ dist pp c ^ 2 := by
        rw [hdist c hc] at h6
        exact max_le (sq_nonneg _) (by linarith)
      calc Real.sqrt (max 0 (I ^ 2 - K)) ≤ Real.sqrt (dist pp c ^ 2) := Real.sqrt_le_sqrt h7
        _ = dist pp c := Real.sqrt_sq dist_nonneg
    have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    rw [Real.sq_sqrt (le_max_left _ _)] at h4
    have := le_max_right 0 (I ^ 2 - K)
    linarith
  linarith

theorem solution {n d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0)
    (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty)
    (hCX : C ⊆ LinearMap.range (Matrix.toEuclideanLin X)) :
    distSq B C = frobSq (B * Y) + distSq (B * X * Xᵀ) C := by
  unfold distSq frobSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := tcd9_inf hjd X Y hX hY hXY C hC hCX (B i)
  have e1 : row B i = WithLp.toLp 2 (B i) := rfl
  have e2 : row (B * X * Xᵀ) i = WithLp.toLp 2 (B i ᵥ* (X * Xᵀ)) := by
    simp [row, Matrix.mul_assoc, Matrix.vecMul_vecMul]
    rfl
  rw [e1, e2, this]
  congr 1
  simp [dotProduct, sq, Matrix.vecMul, Matrix.mul_apply]
