-- Prove2me | solution 1 for YeIPA.Center.proximity_measures_dominated
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:29:47.867814+00:00
-- url     : https://prove2.me/submissions/90ff1156-7c5a-4406-8568-00912e95fa3f

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


/-- Theorem 3.2 (i) (Ye 1997, p. 84). Under the standing assumptions (rank `A = m`, `n > m`,
Ω bounded with nonempty interior; pp. 48, 81), let `(y, s)` be an interior point of Ω and `x`
an interior point of `X_Ω`. Then `η_d(s) ≤ η(x, s)` and `η_p(x) ≤ η(x, s)`. Conversely, if
`η_d(s) < 1` there is an interior point `x'` of `X_Ω` with `η(x', s) ≤ η_d(s)`, and if
`η_p(x) < 1` there is an interior point `(y', s')` of Ω with `η(x, s') ≤ η_p(x)`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (hA : StandingAssumptions A c)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A x) :
    etaD A s ≤ eta x s ∧ etaP A c x ≤ eta x s ∧
      (etaD A s < 1 → ∃ x' : Fin n → ℝ, IsPrimalInterior A x' ∧ eta x' s ≤ etaD A s) ∧
      (etaP A c x < 1 → ∃ (y' : Fin m → ℝ) (s' : Fin n → ℝ),
        IsDualInterior A c y' s' ∧ eta x s' ≤ etaP A c x) := by
  obtain ⟨hsl, hs0⟩ := hs
  obtain ⟨hAx, hx0⟩ := hx
  have hr := hA.1
  have hsj : ∀ j, s j = c j - (Aᵀ *ᵥ y) j := fun j => by rw [hsl]; rfl
  -- dual side data
  set xi : Fin n → ℝ := fun j => (s j)⁻¹ with hxi
  have hxi0 : ∀ j, 0 < xi j := fun j => inv_pos.2 (hs0 j)
  set M := A * diagonal xi * diagonal xi * Aᵀ with hM
  have hU := g70ye_Munit A hr xi hxi0
  set p := dualProxVec A s with hpdef
  have hpm : p = -((diagonal xi * Aᵀ * (A * diagonal xi * diagonal xi * Aᵀ)⁻¹ * A *
      diagonal xi) *ᵥ ones n) := by simp only [hpdef, dualProxVec, diagInv]; rfl
  have hp : p = -(diagonal xi *ᵥ (Aᵀ *ᵥ (M⁻¹ *ᵥ (A *ᵥ (diagonal xi *ᵥ ones n))))) := by
    simp only [hpdef, dualProxVec, diagInv, ← mulVec_mulVec]; rfl
  have hAp : A *ᵥ (diagonal xi *ᵥ p) = -(A *ᵥ (diagonal xi *ᵥ ones n)) := by
    rw [hp, mulVec_neg, mulVec_neg]
    congr 1
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    rw [show A * diagonal xi * diagonal xi * Aᵀ = M from rfl, mulVec_mulVec,
      mul_nonsing_inv _ hU, one_mulVec]
  -- primal side data
  set Mx := A * diagonal x * diagonal x * Aᵀ with hMx
  set P := diagonal x * Aᵀ * Mx⁻¹ * A * diagonal x with hP
  set q := primalProxVec A c x with hqdef
  have hq : q = (1 - P) *ᵥ (diagonal x *ᵥ c - ones n) := rfl
  set y0 := Mx⁻¹ *ᵥ (A *ᵥ (diagonal x *ᵥ (diagonal x *ᵥ c - ones n))) with hy0
  have hq' : q = (diagonal x *ᵥ c - ones n) - diagonal x *ᵥ (Aᵀ *ᵥ y0) := by
    rw [hq, sub_mulVec, one_mulVec]; simp only [hP, hy0, ← mulVec_mulVec]
  have hsqrt_le : ∀ u v : Fin n → ℝ, ∑ j, u j ^ 2 ≤ ∑ j, v j ^ 2 → norm2 u ≤ norm2 v :=
    fun u v h => Real.sqrt_le_sqrt h
  refine ⟨?_, ?_, fun hη => ?_, fun hη => ?_⟩
  · -- eta_d ≤ eta
    have hw : A *ᵥ (diagonal xi *ᵥ (fun j => x j * s j)) = 0 := by
      have : diagonal xi *ᵥ (fun j => x j * s j) = x := by
        funext j; simp only [mulVec_diagonal, hxi]; field_simp [(hs0 j).ne']
      rw [this, hAx]
    have h := g70ye_projle A hr xi hxi0 (ones n) _ hw
    apply hsqrt_le
    show ∑ j, p j ^ 2 ≤ _
    rw [hpm]
    simp only [Pi.neg_apply, neg_sq]
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    simp only [ones]; ring
  · -- eta_p ≤ eta
    have h := g70ye_projle2 A hr x hx0 (diagonal x *ᵥ c - ones n) y
    apply hsqrt_le
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    simp only [Pi.sub_apply, mulVec_diagonal, ones]
    rw [hsj j]; ring
  · -- converse dual
    have hpN : ∀ j, |p j| ≤ etaD A s := fun j => Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    refine ⟨diagonal xi *ᵥ (ones n + p), ⟨?_, fun j => ?_⟩, le_of_eq ?_⟩
    · rw [mulVec_add, mulVec_add, hAp]; abel
    · simp only [mulVec_diagonal, Pi.add_apply, ones]
      have := (abs_le.1 (hpN j)).1
      exact mul_pos (hxi0 j) (by linarith)
    · unfold eta etaD norm2
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [mulVec_diagonal, Pi.add_apply, ones, hxi]
      field_simp [(hs0 j).ne']; ring
  · -- converse primal
    have hqN : ∀ j, |q j| ≤ etaP A c x := fun j => Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun i => q i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    have hxs' : ∀ j, x j * slack A c y0 j = 1 + q j := by
      intro j
      have hj := congrFun hq' j
      simp only [Pi.sub_apply, mulVec_diagonal, ones] at hj
      simp only [slack, Pi.sub_apply]; linarith
    refine ⟨y0, slack A c y0, ⟨rfl, fun j => ?_⟩, le_of_eq ?_⟩
    · have := (abs_le.1 (hqN j)).1
      have h1 : 0 < x j * slack A c y0 j := by rw [hxs' j]; linarith
      exact pos_of_mul_pos_right h1 (hx0 j).le
    · unfold eta etaP norm2
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      show (x j * slack A c y0 j - 1) ^ 2 = q j ^ 2
      rw [hxs' j]; ring



