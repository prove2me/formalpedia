-- Prove2me | solution 1 for WeilDefect.MarkerStability.nonnegative_iff_shell_and_cross_budget
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:11:47.985512+00:00
-- url     : https://prove2.me/submissions/2fe95bfb-cd13-435e-b972-7b435113b3be

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem nonnegative_operator_pair_cauchy_schwarz (A : K →L[ℂ] K) (hA : 0 ≤ A)
    (u z : K) :
    ‖⟪A u, z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪A u, u⟫_ℂ * RCLike.re ⟪A z, z⟫_ℂ := by
  let B := CFC.sqrt A
  have hB : B.adjoint = B := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hBB : B ∘L B = A := CFC.sqrt_mul_sqrt_self A hA
  have he : ∀ x : K, ‖B x‖ ^ 2 = RCLike.re ⟪A x, x⟫_ℂ := by
    intro x
    have h := B.adjoint.apply_norm_sq_eq_inner_adjoint_left x
    simpa only [hB, ← ContinuousLinearMap.comp_apply, hBB] using h
  have hi : ⟪A u, z⟫_ℂ = ⟪B u, B z⟫_ℂ := by
    calc
      _ = ⟪B.adjoint (B u), z⟫_ℂ := by rw [hB, ← ContinuousLinearMap.comp_apply, hBB]
      _ = _ := B.adjoint_inner_left z (B u)
  have hb := pow_le_pow_left₀ (norm_nonneg (⟪B u, B z⟫_ℂ)) (norm_inner_le_norm (𝕜 := ℂ) (B u) (B z)) 2
  calc
    _ = ‖⟪B u, B z⟫_ℂ‖ ^ 2 := congrArg (fun w : ℂ => ‖w‖ ^ 2) hi
    _ ≤ (‖B u‖ * ‖B z‖) ^ 2 := hb
    _ = _ := by rw [mul_pow, he u, he z]

/-- Exact real quadratic expansion with its original self-adjoint cross term. -/
private theorem selfAdjoint_quadratic_add (A : K →L[ℂ] K) (hA : IsSelfAdjoint A) (u z : K) :
    RCLike.re ⟪A (u + z), u + z⟫_ℂ =
      RCLike.re ⟪A u, u⟫_ℂ + 2 * RCLike.re ⟪A u, z⟫_ℂ + RCLike.re ⟪A z, z⟫_ℂ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hc : RCLike.re ⟪A z, u⟫_ℂ = RCLike.re ⟪A u, z⟫_ℂ := by
    exact (congrArg (fun w : ℂ => RCLike.re w) (hs z u)).trans (inner_re_symm z (A u))
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hc]
  ring

theorem solution (A : K →L[ℂ] K)
    (hA : IsSelfAdjoint A) (U : H →ₗᵢ[ℂ] K)
    (hcore : ∀ x : H, 0 ≤ RCLike.re ⟪A (U x), U x⟫_ℂ) :
    0 ≤ A ↔
    (∀ z : K, U.toContinuousLinearMap.adjoint z = 0 → 0 ≤ RCLike.re ⟪A z, z⟫_ℂ) ∧
    (∀ x : H, ∀ z : K, U.toContinuousLinearMap.adjoint z = 0 →
      ‖⟪A (U x), z⟫_ℂ‖ ^ 2 ≤
        RCLike.re ⟪A (U x), U x⟫_ℂ * RCLike.re ⟪A z, z⟫_ℂ) := by
  constructor
  · intro ha
    exact ⟨fun z _ => ((ContinuousLinearMap.nonneg_iff_isPositive A).mp ha).re_inner_nonneg_left z,
      fun x z _ => nonnegative_operator_pair_cauchy_schwarz A ha (U x) z⟩
  · rintro ⟨hshell, hcross⟩
    apply (ContinuousLinearMap.nonneg_iff_isPositive A).mpr
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨hA, ?_⟩
    intro y
    let x := U.toContinuousLinearMap.adjoint y
    let z := y - U x
    have hUU : U.toContinuousLinearMap.adjoint ∘L U.toContinuousLinearMap = 1 :=
      U.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp U.norm_map
    have hz : U.toContinuousLinearMap.adjoint z = 0 := by
      change U.toContinuousLinearMap.adjoint (y - U.toContinuousLinearMap x) = 0
      rw [map_sub]
      change x - (U.toContinuousLinearMap.adjoint ∘L U.toContinuousLinearMap) x = 0
      rw [hUU, one_apply_eq_self, sub_self]
    have hy : y = U x + z := by dsimp [z]; abel
    have ha := hcore x
    have hb := hshell z hz
    have hc := hcross x z hz
    have hsum : 2 * ‖⟪A (U x), z⟫_ℂ‖ ≤
        RCLike.re ⟪A (U x), U x⟫_ℂ + RCLike.re ⟪A z, z⟫_ℂ := by
      apply (sq_le_sq₀ (by positivity) (add_nonneg ha hb)).mp
      nlinarith [sq_nonneg (RCLike.re ⟪A (U x), U x⟫_ℂ - RCLike.re ⟪A z, z⟫_ℂ)]
    have hr : -‖⟪A (U x), z⟫_ℂ‖ ≤ RCLike.re ⟪A (U x), z⟫_ℂ :=
      (abs_le.mp (RCLike.abs_re_le_norm ⟪A (U x), z⟫_ℂ)).1
    change 0 ≤ RCLike.re ⟪A y, y⟫_ℂ
    rw [hy, selfAdjoint_quadratic_add A hA]
    linarith
