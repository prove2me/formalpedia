-- Prove2me | solution 1 for TrustIPM.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:17:58.666655+00:00
-- url     : https://prove2.me/submissions/19c09dc8-7660-407a-9d1e-55e5a76dfb7b

import Mathlib
import Definitions.Def_TrustIPM_HasLipDerivOn

open TrustIPM in
theorem solution (g : ℝ → ℝ) (p : ℕ) (L : ℝ) (S : Set ℝ) (hL : 0 < L) (hS : IsOpen S)
    (hdiff : ∀ k ≤ p, ∀ θ ∈ S, DifferentiableAt ℝ (iteratedDeriv k g) θ) :
    HasLipDerivOn p L g S ↔ ∀ θ ∈ S, |iteratedDeriv (p + 1) g θ| ≤ L := by
  rw [iteratedDeriv_succ]
  constructor
  · intro hlip θ hθ
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS θ hθ
    have hconv : (Metric.ball θ ε).OrdConnected := (convex_ball θ ε).ordConnected
    have hl : LipschitzOnWith L.toNNReal (iteratedDeriv p g) (Metric.ball θ ε) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL.le]
      rcases le_total x y with hxy | hxy
      · exact hlip x y hxy ((hconv.out hx hy).trans hball)
      · rw [abs_sub_comm (iteratedDeriv p g x), abs_sub_comm x]
        exact hlip y x hxy ((hconv.out hy hx).trans hball)
    have := norm_deriv_le_of_lipschitzOn (Metric.ball_mem_nhds θ hε) hl
    rw [Real.norm_eq_abs, Real.coe_toNNReal L hL.le] at this
    exact this
  · intro hb θ₁ θ₂ h12 hsub
    have hd : ∀ x ∈ Set.Icc θ₁ θ₂, DifferentiableAt ℝ (iteratedDeriv p g) x :=
      fun x hx => hdiff p le_rfl x (hsub hx)
    have hbd : ∀ x ∈ Set.Icc θ₁ θ₂, ‖deriv (iteratedDeriv p g) x‖ ≤ L :=
      fun x hx => by rw [Real.norm_eq_abs]; exact hb x (hsub hx)
    have := Convex.norm_image_sub_le_of_norm_deriv_le hd hbd (convex_Icc θ₁ θ₂)
      (Set.right_mem_Icc.mpr h12) (Set.left_mem_Icc.mpr h12)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this
