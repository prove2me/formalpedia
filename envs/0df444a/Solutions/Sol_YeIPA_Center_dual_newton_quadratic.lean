-- Prove2me | solution 1 for YeIPA.Center.dual_newton_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:26:31.643887+00:00
-- url     : https://prove2.me/submissions/07e53e0a-a7fd-4cae-b090-04fc81faefd1

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


/-- Theorem 3.3 (Ye 1997, p. 88). Under the standing assumptions (pp. 48, 81), let `(y, s)` be
an interior point of Ω with `η_d(s) < 1`, and let `s⁺ = s + d_s` with the dual Newton
direction `d_s = Aᵀ(AS⁻²Aᵀ)⁻¹AS⁻¹e` of (3.9). Then `s⁺ > 0` and `η_d(s⁺) ≤ η_d(s)²`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : StandingAssumptions A c) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hs : IsDualInterior A c y s) (hη : etaD A s < 1) :
    (∀ j, 0 < dualNewtonStep A s j) ∧ etaD A (dualNewtonStep A s) ≤ etaD A s ^ 2 := by
  obtain ⟨hsl, hs0⟩ := hs
  have hr := hA.1
  set xi : Fin n → ℝ := fun j => (s j)⁻¹ with hxi
  have hxi0 : ∀ j, 0 < xi j := fun j => inv_pos.2 (hs0 j)
  set M := A * diagonal xi * diagonal xi * Aᵀ with hM
  have hU := g70ye_Munit A hr xi hxi0
  set p := dualProxVec A s with hpdef
  have hp : p = -(diagonal xi *ᵥ (Aᵀ *ᵥ (M⁻¹ *ᵥ (A *ᵥ (diagonal xi *ᵥ ones n))))) := by
    simp only [hpdef, dualProxVec, diagInv, ← mulVec_mulVec]; rfl
  have hdn : dualNewtonDir A s = Aᵀ *ᵥ (M⁻¹ *ᵥ (A *ᵥ (diagonal xi *ᵥ ones n))) := by
    simp only [dualNewtonDir, diagInv, ← mulVec_mulVec]; rfl
  have hdj : ∀ j, dualNewtonDir A s j = -(s j * p j) := by
    intro j; rw [hdn, hp]; simp only [Pi.neg_apply, mulVec_diagonal, hxi]
    field_simp [(hs0 j).ne']
  set N := etaD A s with hN
  have hpN : ∀ j, |p j| ≤ N := fun j => Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hpos1 : ∀ j, 0 < 1 - p j := fun j => by
    have := (abs_le.1 (hpN j)).2; linarith
  have hsp : ∀ j, dualNewtonStep A s j = s j * (1 - p j) := by
    intro j; simp only [dualNewtonStep, Pi.add_apply, hdj]; ring
  have hsp0 : ∀ j, 0 < dualNewtonStep A s j := fun j => by
    rw [hsp j]; exact mul_pos (hs0 j) (hpos1 j)
  refine ⟨hsp0, ?_⟩
  -- the new proximity vector
  set s' := dualNewtonStep A s with hs'
  set xi' : Fin n → ℝ := fun j => (s' j)⁻¹ with hxi'
  have hxi'0 : ∀ j, 0 < xi' j := fun j => inv_pos.2 (hsp0 j)
  set w : Fin n → ℝ := fun j => 1 - p j ^ 2 with hw
  have hAp : A *ᵥ (diagonal xi *ᵥ p) = -(A *ᵥ (diagonal xi *ᵥ ones n)) := by
    rw [hp, mulVec_neg, mulVec_neg]
    congr 1
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    rw [show A * diagonal xi * diagonal xi * Aᵀ = M from rfl, mulVec_mulVec,
      mul_nonsing_inv _ hU, one_mulVec]
  have hw0 : A *ᵥ (diagonal xi' *ᵥ w) = 0 := by
    have e : diagonal xi' *ᵥ w = diagonal xi *ᵥ ones n + diagonal xi *ᵥ p := by
      funext j; simp only [mulVec_diagonal, Pi.add_apply, hxi', hxi, hw, ones]
      rw [hsp j]; have := hpos1 j; have := hs0 j; field_simp; ring
    rw [e, mulVec_add, hAp]; abel
  have hle := g70ye_projle A hr xi' hxi'0 (ones n) w hw0
  have hdp : dualProxVec A s' = -((diagonal xi' * Aᵀ * (A * diagonal xi' * diagonal xi' * Aᵀ)⁻¹ *
      A * diagonal xi') *ᵥ ones n) := by simp only [dualProxVec, diagInv]; rfl
  have hsq : ∑ j, (dualProxVec A s' j) ^ 2 ≤ ∑ j, p j ^ 4 := by
    rw [hdp]
    simp only [Pi.neg_apply, neg_sq]
    refine hle.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => by simp only [ones, hw]; ring
  have hN2 : N ^ 2 = ∑ j, p j ^ 2 := by
    rw [hN, etaD, norm2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have h4 : ∑ j, p j ^ 4 ≤ (N ^ 2) ^ 2 := by
    rw [hN2, sq, Finset.sum_mul_sum]
    calc ∑ j, p j ^ 4 = ∑ j, p j ^ 2 * p j ^ 2 := Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ i, ∑ j, p i ^ 2 * p j ^ 2 := Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (f := fun j => p i ^ 2 * p j ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)
  show norm2 (dualProxVec A s') ≤ N ^ 2
  unfold norm2
  calc Real.sqrt (∑ j, (dualProxVec A s' j) ^ 2) ≤ Real.sqrt ((N ^ 2) ^ 2) :=
        Real.sqrt_le_sqrt (hsq.trans h4)
    _ = N ^ 2 := Real.sqrt_sq (by positivity)



