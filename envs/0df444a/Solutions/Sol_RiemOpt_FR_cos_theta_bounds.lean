-- Prove2me | solution 1 for RiemOpt.FR.cos_theta_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:59:50.942986+00:00
-- url     : https://prove2.me/submissions/419ec784-8801-44d5-ac33-20ea36c62fb8

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace Aux_RiemOpt_CT

lemma key (c₂ u w : ℝ) (hc0 : 0 < c₂) (hc : c₂ < 1 / 2)
    (hu1 : -1 / (1 - c₂) ≤ u) (hu2 : u ≤ (2 * c₂ - 1) / (1 - c₂)) (hw : |w| ≤ -(c₂ * u)) :
    -1 / (1 - c₂) ≤ -1 + w ∧ -1 + w ≤ (2 * c₂ - 1) / (1 - c₂) := by
  have h1c : 0 < 1 - c₂ := by linarith
  rw [div_le_iff₀ h1c] at hu1
  rw [le_div_iff₀ h1c] at hu2
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  constructor
  · rw [div_le_iff₀ h1c]
    nlinarith [mul_le_mul_of_nonneg_right hw1 h1c.le, mul_le_mul_of_nonneg_left hu1 hc0.le]
  · rw [le_div_iff₀ h1c]
    nlinarith [mul_le_mul_of_nonneg_right hw2 h1c.le, mul_le_mul_of_nonneg_left hu1 hc0.le]

end Aux_RiemOpt_CT

namespace Aux_RiemOpt_CT
open RiemOpt.FR
theorem l14 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2) :
    ∀ k : ℕ, -1 / (1 - c₂) ≤ RiemOpt.BFGS.Df (E := E) f (x k) (p k) / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 ∧
      RiemOpt.BFGS.Df (E := E) f (x k) (p k) / ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 ≤ (2 * c₂ - 1) / (1 - c₂) := by
  have hc0 : 0 < c₂ := lt_trans hrun.c₁_pos hrun.c₁_lt_c₂
  have h1c : 0 < 1 - c₂ := by linarith
  have hDf : ∀ y : M, RiemOpt.BFGS.Df (E := E) f y = innerSL ℝ (grad y) := by
    intro y
    ext v
    rw [innerSL_apply_apply]
    exact (hrun.isGradient y v).symm
  have hgg : ∀ y : M, RiemOpt.BFGS.Df (E := E) f y (grad y) =
      ‖RiemOpt.BFGS.Df (E := E) f y‖ ^ 2 := by
    intro y
    rw [hDf y, innerSL_apply_norm, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have hpos : ∀ k, 0 < ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 := by
    intro k
    have h0 := hrun.nonstationary k
    have hne : ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ≠ 0 := fun h =>
      h0 ((ContinuousLinearMap.opNorm_zero_iff _).mp h)
    have : 0 < ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ :=
      lt_of_le_of_ne (ContinuousLinearMap.opNorm_nonneg _) (Ne.symm hne)
    positivity
  intro k
  induction k with
  | zero =>
    have ht : RiemOpt.BFGS.Df (E := E) f (x 0) (p 0) /
        ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 2 = -1 := by
      rw [hrun.dir_zero, map_neg, hgg, neg_div, div_self (hpos 0).ne']
    rw [ht]
    constructor
    · rw [div_le_iff₀ h1c]; linarith
    · rw [le_div_iff₀ h1c]; linarith
  | succ k ih =>
    set N := ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 2 with hN
    set N' := ‖RiemOpt.BFGS.Df (E := E) f (x (k + 1))‖ ^ 2 with hN'
    set a := RiemOpt.BFGS.Df (E := E) f (x k) (p k) with ha
    set b := RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (transportedDir R x p α k) with hb
    have hNpos : 0 < N := hpos k
    have hN'pos : 0 < N' := hpos (k + 1)
    have hstepT : b = RiemOpt.BFGS.Df (E := E) f (R (x k) (α k • p k))
        (RiemOpt.BFGS.transport R (x k) (α k • p k) (p k)) := by
      rw [hb]
      unfold transportedDir
      exact congrArg (fun z : M => RiemOpt.BFGS.Df (E := E) f z
        (RiemOpt.BFGS.transport R (x k) (α k • p k) (p k) : E)) (hrun.step k)
    have hW := (hrun.strongWolfe k).2
    rw [← hstepT] at hW
    have hnext : RiemOpt.BFGS.Df (E := E) f (x (k + 1)) (p (k + 1)) / N' = -1 + b / N := by
      rw [hrun.dir_succ k, map_add, map_neg, map_smul, hgg, smul_eq_mul, ← hN', ← hN, ← hb]
      field_simp <;> ring
    rw [hnext]
    apply Aux_RiemOpt_CT.key c₂ (a / N) (b / N) hc0 hc₂ ih.1 ih.2
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have : -(c₂ * (a / N)) * N = -(c₂ * a) := by field_simp
    rw [this]
    exact hW

end Aux_RiemOpt_CT

open RiemOpt.FR in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2) :
    ∀ k : ℕ, (1 - 2 * c₂) / (1 - c₂) * (‖RiemOpt.BFGS.Df (E := E) f (x k)‖ / ‖p k‖) ≤ cosTheta f x p k ∧
      cosTheta f x p k ≤ 1 / (1 - c₂) * (‖RiemOpt.BFGS.Df (E := E) f (x k)‖ / ‖p k‖) := by
  intro k
  obtain ⟨h1, h2⟩ := Aux_RiemOpt_CT.l14 f R grad c₁ c₂ x p α hrun hc₂ k
  have hc0 : 0 < c₂ := lt_trans hrun.c₁_pos hrun.c₁_lt_c₂
  have h1c : 0 < 1 - c₂ := by linarith
  set n := ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ with hn
  set a := RiemOpt.BFGS.Df (E := E) f (x k) (p k) with ha
  have hn0 : n ≠ 0 := by
    intro h
    exact hrun.nonstationary k ((ContinuousLinearMap.opNorm_zero_iff _).mp h)
  have hnn : 0 ≤ n := ContinuousLinearMap.opNorm_nonneg _
  have hcos : cosTheta f x p k = -(a / n ^ 2) * (n / ‖p k‖) := by
    unfold cosTheta
    rw [← hn, ← ha]
    by_cases hq : ‖p k‖ = 0
    · rw [hq]; simp
    · field_simp
  have hr : 0 ≤ n / ‖p k‖ := div_nonneg hnn (norm_nonneg _)
  rw [hcos]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hr
    have : (1 - 2 * c₂) / (1 - c₂) = -((2 * c₂ - 1) / (1 - c₂)) := by ring
    rw [this]; linarith
  · apply mul_le_mul_of_nonneg_right _ hr
    have : 1 / (1 - c₂) = -(-1 / (1 - c₂)) := by ring
    rw [this]; linarith
