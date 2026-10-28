-- Prove2me | solution 1 for SmoothCCP.PenaltyModel.linearization_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:57:49.161993+00:00
-- url     : https://prove2.me/submissions/7dd2dda0-71ea-4349-8248-5fa0eb5d9c86

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace Aux_SCCP_lin

open InnerProductSpace

lemma taylor {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f) (L' : ℝ) (hL0 : 0 ≤ L')
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L' * ‖x - y‖)
    (x d : EuclideanSpace ℝ (Fin n)) :
    |f (x + d) - f x - inner ℝ (gradient f x) d| ≤ L' * ‖d‖ ^ 2 := by
  set g0 := gradient f x
  let φ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => f y - toDual ℝ _ g0 y
  have hder : ∀ y ∈ segment ℝ x (x + d), HasFDerivWithinAt φ
      (toDual ℝ _ (gradient f y - g0)) (segment ℝ x (x + d)) y := by
    intro y _
    have h1 : HasFDerivAt f (toDual ℝ _ (gradient f y)) y :=
      hasGradientAt_iff_hasFDerivAt.mp (hf y).hasGradientAt
    have h2 := h1.sub (toDual ℝ _ g0).hasFDerivAt
    rw [← map_sub] at h2
    exact h2.hasFDerivWithinAt
  have hbound : ∀ y ∈ segment ℝ x (x + d), ‖toDual ℝ _ (gradient f y - g0)‖ ≤ L' * ‖d‖ := by
    intro y hy
    rw [LinearIsometryEquiv.norm_map]
    refine le_trans (hL y x) ?_
    apply mul_le_mul_of_nonneg_left _ hL0
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    have : a • x + b • (x + d) - x = b • d := by
      rw [smul_add, ← add_assoc, ← add_smul, hab, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    calc b * ‖d‖ ≤ 1 * ‖d‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = ‖d‖ := one_mul _
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound
    (convex_segment x (x + d)) (left_mem_segment ℝ x (x + d)) (right_mem_segment ℝ x (x + d))
  simp only [φ, toDual_apply_apply, add_sub_cancel_left, Real.norm_eq_abs] at hmvt
  have e : f (x + d) - inner ℝ g0 (x + d) - (f x - inner ℝ g0 x) =
      f (x + d) - f x - inner ℝ g0 d := by
    rw [inner_add_right]; ring
  rw [e] at hmvt
  calc _ ≤ L' * ‖d‖ * ‖d‖ := hmvt
    _ = L' * ‖d‖ ^ 2 := by ring

lemma sup_diff {m : ℕ} (s : Finset (Fin m)) (hs : s.Nonempty) (a b : Fin m → ℝ) (K : ℝ)
    (h : ∀ j, |a j - b j| ≤ K) : |s.sup' hs a - s.sup' hs b| ≤ K := by
  rw [abs_le]
  constructor
  · have : s.sup' hs b ≤ s.sup' hs a + K := by
      apply Finset.sup'_le
      intro j hj
      have := (abs_le.mp (h j)).1
      have := Finset.le_sup' a hj
      linarith
    linarith
  · have : s.sup' hs a ≤ s.sup' hs b + K := by
      apply Finset.sup'_le
      intro j hj
      have := (abs_le.mp (h j)).2
      have := Finset.le_sup' b hj
      linarith
    linarith

end Aux_SCCP_lin

open SmoothCCP.PenaltyModel in
theorem solution {n m N : ℕ} {Ξ : Type} (hm : 1 ≤ m) (ξs : Fin N → Ξ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L' : ℝ) (hL' : 0 < L')
    (hc : ∀ i j, Differentiable ℝ (fun x => c j x (ξs i)))
    (h55 : ∀ (x y : EuclideanSpace ℝ (Fin n)) (i : Fin N) (j : Fin m),
      ‖gradient (fun z => c j z (ξs i)) x - gradient (fun z => c j z (ξs i)) y‖ ≤ L' * ‖x - y‖)
    (x d : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ i, (CN hm c ξs (x + d) i - Ctil hm c ξs x d i) ^ 2)
      ≤ Real.sqrt N * L' * ‖d‖ ^ 2 := by
  set K := L' * ‖d‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hi : ∀ i, |CN hm c ξs (x + d) i - Ctil hm c ξs x d i| ≤ K := by
    intro i
    unfold CN Ctil
    apply Aux_SCCP_lin.sup_diff
    intro j
    have := Aux_SCCP_lin.taylor (fun z => c j z (ξs i)) (hc i j) L' hL'.le (fun x y => h55 x y i j) x d
    have e : c j (x + d) (ξs i) - (c j x (ξs i) + inner ℝ (gradient (fun y => c j y (ξs i)) x) d) =
        c j (x + d) (ξs i) - c j x (ξs i) - inner ℝ (gradient (fun z => c j z (ξs i)) x) d := by ring
    rw [e]; exact this
  have hsum : ∑ i, (CN hm c ξs (x + d) i - Ctil hm c ξs x d i) ^ 2 ≤ N * K ^ 2 := by
    calc _ ≤ ∑ _i : Fin N, K ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hi i) 2
      _ = N * K ^ 2 := by simp
  calc Real.sqrt (∑ i, (CN hm c ξs (x + d) i - Ctil hm c ξs x d i) ^ 2)
      ≤ Real.sqrt (N * K ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt N * K := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq hK0]
    _ = Real.sqrt N * L' * ‖d‖ ^ 2 := by rw [hK]; ring
