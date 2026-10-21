-- Prove2me | solution 1 for SuttonTD.Convergence.eigenvalues_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:23:35.015867+00:00
-- url     : https://prove2.me/submissions/0bc4036c-44a5-4747-87c8-227fb3a894be

import Mathlib
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal

set_option autoImplicit false
open Matrix SuttonTD.Convergence

theorem solution {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}
    (X : Matrix (Fin K) N ℝ) (hX : LinearIndependent ℝ (fun i : N => fun k : Fin K => X k i))
    (M : Matrix N N ℝ) (hM : IsPosDefReal M) (lam : ℂ) (v : N → ℂ) (hv : v ≠ 0)
    (hev : (Xᵀ * X * M).map (algebraMap ℝ ℂ) *ᵥ v = lam • v) :
    0 < lam.re := by
  have hXinj : ∀ g : N → ℝ, X *ᵥ g = 0 → g = 0 := by
    intro g hg
    rw [Fintype.linearIndependent_iff] at hX
    funext i
    refine hX g ?_ i
    funext k
    have := congrFun hg k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hMinj : ∀ g : N → ℝ, M *ᵥ g = 0 → g = 0 := by
    intro g hg
    by_contra hne
    have := hM g hne
    rw [hg, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hMnn : ∀ g : N → ℝ, 0 ≤ g ⬝ᵥ (M *ᵥ g) := by
    intro g
    by_cases hg : g = 0
    · simp [hg]
    · exact (hM g hg).le
  have hdot : ∀ (u : Fin K → ℝ) (z : N → ℝ), ((Xᵀ *ᵥ u) ⬝ᵥ z) = u ⬝ᵥ (X *ᵥ z) := by
    intro u z
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  set a : N → ℝ := fun j => (v j).re with ha
  set b : N → ℝ := fun j => (v j).im with hb
  set x := lam.re with hx
  set y := lam.im with hy
  have hre : (Xᵀ * X * M) *ᵥ a = x • a - y • b := by
    funext i
    have h := congrArg Complex.re (congrFun hev i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Complex.re_sum, Complex.mul_re] at h
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hb, hx, hy]
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm] using h
  have him : (Xᵀ * X * M) *ᵥ b = y • a + x • b := by
    funext i
    have h := congrArg Complex.im (congrFun hev i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Complex.im_sum, Complex.mul_im] at h
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb, hx, hy]
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, add_comm] using h
  -- real quantities
  set c : N → ℝ := M *ᵥ a with hc
  set d : N → ℝ := M *ᵥ b with hd
  have hBa : (Xᵀ * X * M) *ᵥ a = Xᵀ *ᵥ (X *ᵥ c) := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hBb : (Xᵀ * X * M) *ᵥ b = Xᵀ *ᵥ (X *ᵥ d) := by
    rw [hd, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hBa] at hre
  rw [hBb] at him
  have hdot2 : ∀ (u : N → ℝ) (w : Fin K → ℝ), u ⬝ᵥ (Xᵀ *ᵥ w) = (X *ᵥ u) ⬝ᵥ w := by
    intro u w
    rw [dotProduct_comm, hdot, dotProduct_comm]
  have e1 : (X *ᵥ c) ⬝ᵥ (X *ᵥ c) = x * (c ⬝ᵥ a) - y * (c ⬝ᵥ b) := by
    rw [← hdot2 c (X *ᵥ c), hre, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have e2 : (X *ᵥ d) ⬝ᵥ (X *ᵥ d) = y * (d ⬝ᵥ a) + x * (d ⬝ᵥ b) := by
    rw [← hdot2 d (X *ᵥ d), him, dotProduct_add, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have e3 : (X *ᵥ c) ⬝ᵥ (X *ᵥ d) = y * (c ⬝ᵥ a) + x * (c ⬝ᵥ b) := by
    rw [← hdot2 c (X *ᵥ d), him, dotProduct_add, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have e4 : (X *ᵥ d) ⬝ᵥ (X *ᵥ c) = x * (d ⬝ᵥ a) - y * (d ⬝ᵥ b) := by
    rw [← hdot2 d (X *ᵥ c), hre, dotProduct_sub, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  have e34 : (X *ᵥ c) ⬝ᵥ (X *ᵥ d) = (X *ᵥ d) ⬝ᵥ (X *ᵥ c) := dotProduct_comm _ _
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext j
    apply Complex.ext
    · exact congrFun h.1 j
    · exact congrFun h.2 j
  have hα : 0 < c ⬝ᵥ a + d ⬝ᵥ b := by
    have h1 : c ⬝ᵥ a = a ⬝ᵥ (M *ᵥ a) := dotProduct_comm _ _
    have h2 : d ⬝ᵥ b = b ⬝ᵥ (M *ᵥ b) := dotProduct_comm _ _
    rw [h1, h2]
    rcases hab with h | h
    · have := hM a h
      have := hMnn b
      linarith
    · have := hM b h
      have := hMnn a
      linarith
  have hp : 0 < (X *ᵥ c) ⬝ᵥ (X *ᵥ c) + (X *ᵥ d) ⬝ᵥ (X *ᵥ d) := by
    have hsq : ∀ w : Fin K → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    by_contra hle
    push_neg at hle
    have hc0 : (X *ᵥ c) ⬝ᵥ (X *ᵥ c) = 0 := by
      have := hsq (X *ᵥ c)
      have := hsq (X *ᵥ d)
      linarith
    have hd0 : (X *ᵥ d) ⬝ᵥ (X *ᵥ d) = 0 := by
      have := hsq (X *ᵥ c)
      have := hsq (X *ᵥ d)
      linarith
    have hXc : X *ᵥ c = 0 := dotProduct_self_eq_zero.1 hc0
    have hXd : X *ᵥ d = 0 := dotProduct_self_eq_zero.1 hd0
    have hc' : M *ᵥ a = 0 := hXinj c hXc
    have hd' : M *ᵥ b = 0 := hXinj d hXd
    have ha0 := hMinj a hc'
    have hb0 := hMinj b hd'
    rcases hab with h | h
    · exact h ha0
    · exact h hb0
  have hpe : (X *ᵥ c) ⬝ᵥ (X *ᵥ c) + (X *ᵥ d) ⬝ᵥ (X *ᵥ d)
      = x * (c ⬝ᵥ a + d ⬝ᵥ b) + y * (d ⬝ᵥ a - c ⬝ᵥ b) := by
    rw [e1, e2]; ring
  have hcross : y * (c ⬝ᵥ a + d ⬝ᵥ b) = x * (d ⬝ᵥ a - c ⬝ᵥ b) := by
    rw [e3, e4] at e34
    linarith
  set α := c ⬝ᵥ a + d ⬝ᵥ b with hαdef
  set β := d ⬝ᵥ a - c ⬝ᵥ b with hβdef
  set p := (X *ᵥ c) ⬝ᵥ (X *ᵥ c) + (X *ᵥ d) ⬝ᵥ (X *ᵥ d) with hpdef
  have hpα : p * α = x * (α ^ 2 + β ^ 2) := by
    rw [hpe]
    linear_combination β * hcross
  show 0 < x
  by_contra hxle
  push_neg at hxle
  have h1 : 0 < p * α := mul_pos hp hα
  have h2 : x * (α ^ 2 + β ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hxle (by positivity)
  linarith
