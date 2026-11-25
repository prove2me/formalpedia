-- Prove2me | solution 1 for SSLWithoutPairs.weight_decay_balancing
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:58:09.124663+00:00
-- url     : https://prove2.me/submissions/b7b23eb3-915c-4fdd-9220-66fe3f999b01

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Matrix
namespace SSLWithoutPairs

lemma wd_d1 {m n : ℕ} (A A' : ℝ → Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivWithinAt (fun s => A s i j) (A' t i j) (Set.Ici 0) t) (i j : Fin m) :
    HasDerivWithinAt (fun s => (A s * (A s)ᵀ) i j)
      ((A' t * (A t)ᵀ + A t * (A' t)ᵀ) i j) (Set.Ici 0) t := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
  have := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ => (hA i k).mul (hA j k))
  refine this.congr_deriv ?_
  rw [← Finset.sum_add_distrib]

lemma wd_d2 {m : ℕ} (A A' : ℝ → Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivWithinAt (fun s => A s i j) (A' t i j) (Set.Ici 0) t) (i j : Fin m) :
    HasDerivWithinAt (fun s => ((A s)ᵀ * A s) i j)
      (((A' t)ᵀ * A t + (A t)ᵀ * A' t) i j) (Set.Ici 0) t := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
  have := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun k _ => (hA k i).mul (hA k j))
  refine this.congr_deriv ?_
  rw [← Finset.sum_add_distrib]

theorem weight_decay_balancing {n₁ n₂ : ℕ} (αp η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η)
    (X X' : Matrix (Fin n₁) (Fin n₁) ℝ) (hX : X.PosSemidef) (hX' : X'.PosSemidef)
    (Wp : ℝ → Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : ℝ → Matrix (Fin n₂) (Fin n₁) ℝ)
    (hWp : HasMatDerivOn Wp (fun t => byolFlowWp αp η X X' (Wp t) (W t) (Wa t)))
    (hW : HasMatDerivOn W (fun t => byolFlowW η X X' (Wp t) (W t) (Wa t))) :
    let C : Matrix (Fin n₂) (Fin n₂) ℝ := W 0 * (W 0)ᵀ - αp⁻¹ • ((Wp 0)ᵀ * Wp 0)
    Cᵀ = C ∧ ∀ t : ℝ, 0 ≤ t →
      W t * (W t)ᵀ = αp⁻¹ • ((Wp t)ᵀ * Wp t) + Real.exp (-2 * η * t) • C := by
  intro C
  refine ⟨?_, ?_⟩
  · simp only [C, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  set D : ℝ → Matrix (Fin n₂) (Fin n₂) ℝ := fun t => W t * (W t)ᵀ - αp⁻¹ • ((Wp t)ᵀ * Wp t)
    with hD
  -- derivative of D is -2η D
  have hDd : ∀ t, 0 ≤ t → ∀ i j,
      HasDerivWithinAt (fun s => D s i j) (-2 * η * D t i j) (Set.Ici 0) t := by
    intro t ht i j
    have h1 := wd_d1 W (fun t => byolFlowW η X X' (Wp t) (W t) (Wa t)) t (hW t ht) i j
    have h2 := (wd_d2 Wp (fun t => byolFlowWp αp η X X' (Wp t) (W t) (Wa t)) t (hWp t ht) i j).const_mul αp⁻¹
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    set G := -(Wp t * W t * (X + X')) + Wa t * X with hG
    have eM : (byolFlowW η X X' (Wp t) (W t) (Wa t) * (W t)ᵀ +
          W t * (byolFlowW η X X' (Wp t) (W t) (Wa t))ᵀ) -
        αp⁻¹ • ((byolFlowWp αp η X X' (Wp t) (W t) (Wa t))ᵀ * Wp t +
          (Wp t)ᵀ * byolFlowWp αp η X X' (Wp t) (W t) (Wa t)) = (-2 * η) • D t := by
      simp only [byolFlowW, byolFlowWp, ← hG, hD]
      simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hαp.ne', one_smul,
        Matrix.mul_assoc]
      module
    have := congrFun (congrFun eM i) j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    simp only [Matrix.add_apply]
    linarith
  intro t ht
  have hc : ∀ i j, Real.exp (2 * η * t) * D t i j = D 0 i j := by
    intro i j
    have hd0 : ∀ x, 0 ≤ x → HasDerivWithinAt (fun s => Real.exp (2 * η * s) * D s i j) 0
        (Set.Ici 0) x := by
      intro x hx
      have he : HasDerivWithinAt (fun s => Real.exp (2 * η * s)) (Real.exp (2 * η * x) * (2 * η))
          (Set.Ici 0) x := by
        have := ((hasDerivAt_id x).const_mul (2 * η)).exp
        simpa using this.hasDerivWithinAt
      refine (he.mul (hDd x hx i j)).congr_deriv ?_
      ring
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => Real.exp (2 * η * s) * D s i j) (f' := fun _ => (0:ℝ))
      (C := 0) (a := 0) (b := t)
      (fun x hx => (hd0 x hx.1).mono Set.Icc_subset_Ici_self)
      (fun x _ => by simp) t ⟨ht, le_rfl⟩
    simp only [zero_mul, norm_le_zero_iff, sub_eq_zero, mul_zero, Real.exp_zero, one_mul] at key
    exact key
  have hinv : Real.exp (-2 * η * t) * Real.exp (2 * η * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hDt : D t = Real.exp (-2 * η * t) • C := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    have : C i j = D 0 i j := rfl
    rw [this, ← hc i j, ← mul_assoc, hinv, one_mul]
  have : W t * (W t)ᵀ = D t + αp⁻¹ • ((Wp t)ᵀ * Wp t) := by
    simp only [hD]; abel
  rw [this, hDt, add_comm]

end SSLWithoutPairs

open SSLWithoutPairs in
theorem solution {n₁ n₂ : ℕ} (αp η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η)
    (X X' : Matrix (Fin n₁) (Fin n₁) ℝ) (hX : X.PosSemidef) (hX' : X'.PosSemidef)
    (Wp : ℝ → Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : ℝ → Matrix (Fin n₂) (Fin n₁) ℝ)
    (hWp : HasMatDerivOn Wp (fun t => byolFlowWp αp η X X' (Wp t) (W t) (Wa t)))
    (hW : HasMatDerivOn W (fun t => byolFlowW η X X' (Wp t) (W t) (Wa t))) :
    let C : Matrix (Fin n₂) (Fin n₂) ℝ := W 0 * (W 0)ᵀ - αp⁻¹ • ((Wp 0)ᵀ * Wp 0)
    Cᵀ = C ∧ ∀ t : ℝ, 0 ≤ t →
      W t * (W t)ᵀ = αp⁻¹ • ((Wp t)ᵀ * Wp t) + Real.exp (-2 * η * t) • C :=
  SSLWithoutPairs.weight_decay_balancing αp η hαp hη X X' hX hX' Wp W Wa hWp hW
