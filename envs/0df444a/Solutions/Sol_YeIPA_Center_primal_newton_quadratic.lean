-- Prove2me | solution 1 for YeIPA.Center.primal_newton_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:28:29.124907+00:00
-- url     : https://prove2.me/submissions/42bc0fad-6999-462c-8776-ad5da0f7b144

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix
open YeIPA.Center
theorem g70ye_AAt_unit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) :
    IsUnit (A * Aᵀ).det := by
  have hr : (A * Aᵀ).rank = m := by rw [Matrix.rank_self_mul_transpose]; exact hrank
  have htop : LinearMap.range (A * Aᵀ).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank ℝ (LinearMap.range (A * Aᵀ).mulVecLin) = (A * Aᵀ).rank from rfl, hr]
    simp
  have hsurj : Function.Surjective (A * Aᵀ).mulVec := LinearMap.range_eq_top.mp htop
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)


theorem g70ye_proj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hr : A.rank = m) (x : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (g p : Fin n → ℝ)
    (hp : p = (1 - diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ g) :
    A *ᵥ (diagonal x *ᵥ p) = 0 ∧ p ⬝ᵥ g = p ⬝ᵥ p := by
  set B := A * diagonal x with hBdef
  have hdet : IsUnit (diagonal x).det := by
    rw [det_diagonal]; exact (Finset.prod_pos fun i _ => hx i).ne'.isUnit
  have hrB : B.rank = m := by rw [hBdef, rank_mul_eq_left_of_isUnit_det _ _ hdet, hr]
  have hU := g70ye_AAt_unit B hrB
  have hBt : Bᵀ = diagonal x * Aᵀ := by simp [B, transpose_mul, diagonal_transpose]
  have hM : A * diagonal x * diagonal x * Aᵀ = B * Bᵀ := by
    rw [hBt]; simp only [B, Matrix.mul_assoc]
  have hPm : diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x =
      Bᵀ * (B * Bᵀ)⁻¹ * B := by
    rw [hM, hBt]; simp only [B, Matrix.mul_assoc]
  set w := (B * Bᵀ)⁻¹ *ᵥ (B *ᵥ g)
  have hp' : p = g - Bᵀ *ᵥ w := by
    rw [hp, hPm, sub_mulVec, one_mulVec]; simp only [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hBp : B *ᵥ p = 0 := by
    rw [hp', mulVec_sub, mulVec_mulVec]
    rw [show (B * Bᵀ) *ᵥ w = B *ᵥ g by
      simp only [w, mulVec_mulVec]; rw [← Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.one_mul],
      sub_self]
  have orth : p ⬝ᵥ (Bᵀ *ᵥ w) = (B *ᵥ p) ⬝ᵥ w := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_comm (B *ᵥ p), dotProduct_mulVec]
  refine ⟨by rw [mulVec_mulVec]; exact hBp, ?_⟩
  have hg' : g = p + Bᵀ *ᵥ w := by rw [hp']; abel
  rw [hg', dotProduct_add, orth, hBp, zero_dotProduct, add_zero]

theorem g70ye_Munit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hr : A.rank = m) (x : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) : IsUnit (A * diagonal x * diagonal x * Aᵀ).det := by
  have hdet : IsUnit (diagonal x).det := by
    rw [det_diagonal]; exact (Finset.prod_pos fun i _ => hx i).ne'.isUnit
  have hrB : (A * diagonal x).rank = m := by rw [rank_mul_eq_left_of_isUnit_det _ _ hdet, hr]
  have h := g70ye_AAt_unit (A * diagonal x) hrB
  have e : A * diagonal x * (A * diagonal x)ᵀ = A * diagonal x * diagonal x * Aᵀ := by
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc (A * diagonal x) (diagonal x) Aᵀ]
  rwa [e] at h

theorem g70ye_projle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hr : A.rank = m)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (v w : Fin n → ℝ)
    (hw : A *ᵥ (diagonal x *ᵥ w) = 0) :
    ∑ j, (((diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ v) j) ^ 2
      ≤ ∑ j, (v j - w j) ^ 2 := by
  set P := diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x with hP
  have hPw : P *ᵥ w = 0 := by
    simp only [hP, ← mulVec_mulVec, hw, mulVec_zero]
  have hPv : P *ᵥ v = P *ᵥ (v - w) := by rw [mulVec_sub, hPw, sub_zero]
  set g := v - w with hg
  obtain ⟨-, h2⟩ := g70ye_proj A hr x hx g ((1 - P) *ᵥ g) rfl
  set q := (1 - P) *ᵥ g with hq
  have hq' : g = q + P *ᵥ g := by rw [hq, sub_mulVec, one_mulVec]; abel
  have hcross : q ⬝ᵥ (P *ᵥ g) = 0 := by
    have := h2; rw [hq'] at this
    rw [dotProduct_add] at this
    linarith
  have hgg : g ⬝ᵥ g = q ⬝ᵥ q + (P *ᵥ g) ⬝ᵥ (P *ᵥ g) := by
    conv_lhs => rw [hq']
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hcross, dotProduct_comm (P *ᵥ g) q, hcross]
    ring
  have hqq : 0 ≤ q ⬝ᵥ q := Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have e1 : ∑ j, ((P *ᵥ v) j) ^ 2 = (P *ᵥ g) ⬝ᵥ (P *ᵥ g) := by
    rw [hPv]; simp [dotProduct, sq]
  have e2 : ∑ j, (v j - w j) ^ 2 = g ⬝ᵥ g := by simp [hg, dotProduct, sq]
  rw [e1, e2]; linarith

theorem g70ye_projle2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hr : A.rank = m)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (v : Fin n → ℝ) (z : Fin m → ℝ) :
    ∑ j, (((1 - diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ v) j) ^ 2
      ≤ ∑ j, (v j - (diagonal x *ᵥ (Aᵀ *ᵥ z)) j) ^ 2 := by
  set P := diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x with hP
  have hU := g70ye_Munit A hr x hx
  have hkill : (1 - P) *ᵥ (diagonal x *ᵥ (Aᵀ *ᵥ z)) = 0 := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero]
    simp only [hP, ← mulVec_mulVec]
    have hMM : (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x * diagonal x * Aᵀ = 1 := by
      have := nonsing_inv_mul _ hU; simpa only [Matrix.mul_assoc] using this
    congr 2
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hMM, one_mulVec]
  set g := v - diagonal x *ᵥ (Aᵀ *ᵥ z) with hg
  have hqv : (1 - P) *ᵥ v = (1 - P) *ᵥ g := by rw [hg, mulVec_sub, hkill, sub_zero]
  obtain ⟨-, h2⟩ := g70ye_proj A hr x hx g ((1 - P) *ᵥ g) rfl
  set q := (1 - P) *ᵥ g with hq
  have hq' : g = q + P *ᵥ g := by rw [hq, sub_mulVec, one_mulVec]; abel
  have hcross : q ⬝ᵥ (P *ᵥ g) = 0 := by
    have := h2; rw [hq'] at this
    rw [dotProduct_add] at this
    linarith
  have hgg : g ⬝ᵥ g = q ⬝ᵥ q + (P *ᵥ g) ⬝ᵥ (P *ᵥ g) := by
    conv_lhs => rw [hq']
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hcross, dotProduct_comm (P *ᵥ g) q, hcross]
    ring
  have hPP : 0 ≤ (P *ᵥ g) ⬝ᵥ (P *ᵥ g) := Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have e1 : ∑ j, (((1 - P) *ᵥ v) j) ^ 2 = q ⬝ᵥ q := by
    rw [hqv]; simp [dotProduct, sq]
  have e2 : ∑ j, (v j - (diagonal x *ᵥ (Aᵀ *ᵥ z)) j) ^ 2 = g ⬝ᵥ g := by
    simp [hg, dotProduct, sq]
  rw [e1, e2]; linarith


/-- Corollary 3.8 (Ye 1997, p. 95). Under the standing assumptions (pp. 48, 81), let `x` be an
interior point of `X_Ω` with `η_p(x) < 1`, and let `x⁺ = x + d_x` with the primal Newton
direction `d_x = −X(I − XAᵀ(AX²Aᵀ)⁻¹AX)(Xc − e)` of (3.13). Then `x⁺ > 0`, `Ax⁺ = 0` and
`η_p(x⁺) ≤ η_p(x)²`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : StandingAssumptions A c) (x : Fin n → ℝ) (hx : IsPrimalInterior A x)
    (hη : etaP A c x < 1) :
    (∀ j, 0 < primalNewtonStep A c x j) ∧ A *ᵥ primalNewtonStep A c x = 0 ∧
      etaP A c (primalNewtonStep A c x) ≤ etaP A c x ^ 2 := by
  obtain ⟨hAx, hx0⟩ := hx
  have hr := hA.1
  set M := A * diagonal x * diagonal x * Aᵀ with hM
  set P := diagonal x * Aᵀ * M⁻¹ * A * diagonal x with hP
  set p := primalProxVec A c x with hpdef
  have hp : p = (1 - P) *ᵥ (diagonal x *ᵥ c - ones n) := rfl
  obtain ⟨hproj, -⟩ := g70ye_proj A hr x hx0 (diagonal x *ᵥ c - ones n) p hp
  have hdir : primalNewtonDir A c x = -(diagonal x *ᵥ p) := by
    simp only [primalNewtonDir, ← mulVec_mulVec]; rfl
  set N := etaP A c x with hN
  have hpN : ∀ j, |p j| ≤ N := fun j => Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hpos1 : ∀ j, 0 < 1 - p j := fun j => by
    have := (abs_le.1 (hpN j)).2; linarith
  have hxp : ∀ j, primalNewtonStep A c x j = x j * (1 - p j) := by
    intro j; simp only [primalNewtonStep, Pi.add_apply, hdir, Pi.neg_apply, mulVec_diagonal]; ring
  have hxp0 : ∀ j, 0 < primalNewtonStep A c x j := fun j => by
    rw [hxp j]; exact mul_pos (hx0 j) (hpos1 j)
  refine ⟨hxp0, ?_, ?_⟩
  · simp only [primalNewtonStep, mulVec_add, hAx, hdir, mulVec_neg, hproj, neg_zero, add_zero]
  -- the bound
  set x' := primalNewtonStep A c x with hx'
  set y := M⁻¹ *ᵥ (A *ᵥ (diagonal x *ᵥ (diagonal x *ᵥ c - ones n))) with hy
  have hp' : p = (diagonal x *ᵥ c - ones n) - diagonal x *ᵥ (Aᵀ *ᵥ y) := by
    rw [hp, sub_mulVec, one_mulVec]; simp only [hP, hy, ← mulVec_mulVec]
  have hle := g70ye_projle2 A hr x' hxp0 (diagonal x' *ᵥ c - ones n) y
  have hterm : ∀ j, (diagonal x' *ᵥ c - ones n) j - (diagonal x' *ᵥ (Aᵀ *ᵥ y)) j = -(p j ^ 2) := by
    intro j
    have hj := congrFun hp' j
    simp only [Pi.sub_apply, mulVec_diagonal, ones] at hj ⊢
    rw [hxp j]
    have e : x j * (c j - (Aᵀ *ᵥ y) j) = 1 + p j := by linarith
    have : x j * (1 - p j) * c j - 1 - x j * (1 - p j) * (Aᵀ *ᵥ y) j =
        (1 - p j) * (x j * (c j - (Aᵀ *ᵥ y) j)) - 1 := by ring
    rw [this, e]; ring
  have hsq : ∑ j, (primalProxVec A c x' j) ^ 2 ≤ ∑ j, p j ^ 4 := by
    refine hle.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [hterm j]; ring
  have hN2 : N ^ 2 = ∑ j, p j ^ 2 := by
    rw [hN, etaP, norm2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have h4 : ∑ j, p j ^ 4 ≤ (N ^ 2) ^ 2 := by
    rw [hN2, sq, Finset.sum_mul_sum]
    calc ∑ j, p j ^ 4 = ∑ j, p j ^ 2 * p j ^ 2 := Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ i, ∑ j, p i ^ 2 * p j ^ 2 := Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (f := fun j => p i ^ 2 * p j ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)
  show norm2 (primalProxVec A c x') ≤ N ^ 2
  unfold norm2
  calc Real.sqrt (∑ j, (primalProxVec A c x' j) ^ 2) ≤ Real.sqrt ((N ^ 2) ^ 2) :=
        Real.sqrt_le_sqrt (hsq.trans h4)
    _ = N ^ 2 := Real.sqrt_sq (by positivity)



