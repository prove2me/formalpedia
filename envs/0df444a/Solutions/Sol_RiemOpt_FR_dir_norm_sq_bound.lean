-- Prove2me | solution 1 for RiemOpt.FR.dir_norm_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:02:43.60493+00:00
-- url     : https://prove2.me/submissions/7206cda6-2a36-418d-b718-28b014f1c25c

import Mathlib
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold
open scoped ContDiff

namespace Aux_RiemOpt_DN

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

end Aux_RiemOpt_DN

namespace Aux_RiemOpt_DN
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
    apply Aux_RiemOpt_DN.key c₂ (a / N) (b / N) hc0 hc₂ ih.1 ih.2
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have : -(c₂ * (a / N)) * N = -(c₂ * a) := by field_simp
    rw [this]
    exact hW

end Aux_RiemOpt_DN

open RiemOpt.FR in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (f : M → ℝ) (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (c₁ c₂ : ℝ)
    (x : ℕ → M) (p : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) (α : ℕ → ℝ)
    (hrun : IsFRRun f R grad c₁ c₂ x p α) (hc₂ : c₂ < 1 / 2)
    (hT : ∀ k : ℕ, ‖transportedDir R x p α k‖ ≤ ‖p k‖) :
    ∀ k : ℕ, ‖p k‖ ^ 2 ≤ (1 + c₂) / (1 - c₂) * ‖RiemOpt.BFGS.Df (E := E) f (x k)‖ ^ 4 *
      ∑ j ∈ Finset.range (k + 1), (‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 2)⁻¹ := by
  have hc0 : 0 < c₂ := lt_trans hrun.c₁_pos hrun.c₁_lt_c₂
  have h1c : 0 < 1 - c₂ := by linarith
  set C := (1 + c₂) / (1 - c₂) with hC
  have hC1 : 1 ≤ C := by rw [hC, le_div_iff₀ h1c]; linarith
  have hDf : ∀ y : M, RiemOpt.BFGS.Df (E := E) f y = innerSL ℝ (grad y) := by
    intro y
    ext v
    rw [innerSL_apply_apply]
    exact (hrun.isGradient y v).symm
  have hng : ∀ y : M, ‖grad y‖ = ‖RiemOpt.BFGS.Df (E := E) f y‖ := by
    intro y; rw [hDf y, innerSL_apply_norm]
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
    rw [hrun.dir_zero, norm_neg, hng, Finset.sum_range_one]
    have hN := hpos 0
    set N := ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 2 with hNdef
    have e : ‖RiemOpt.BFGS.Df (E := E) f (x 0)‖ ^ 4 = N ^ 2 := by rw [hNdef]; ring
    rw [e]
    have : C * N ^ 2 * N⁻¹ = C * N := by field_simp
    rw [this]
    nlinarith
  | succ k ih =>
    have hl := Aux_RiemOpt_DN.l14 f R grad c₁ c₂ x p α hrun hc₂ k
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
    -- -a ≤ N / (1 - c₂)
    have ha1 : -a ≤ N / (1 - c₂) := by
      have h := hl.1
      rw [div_le_div_iff₀ h1c hNpos] at h
      rw [le_div_iff₀ h1c]
      linarith
    have hbb : -b ≤ c₂ * (N / (1 - c₂)) := by
      have := neg_le_abs b
      nlinarith
    set β := N' / N with hβ
    have hβN : β * N = N' := by rw [hβ]; field_simp
    have hβ0 : 0 ≤ β := div_nonneg hN'pos.le hNpos.le
    -- expand ‖p (k+1)‖^2
    have hinner : inner ℝ (grad (x (k + 1))) (transportedDir R x p α k) = b := by
      rw [hb]; exact hrun.isGradient _ _
    have hexp : ‖p (k + 1)‖ ^ 2 = N' - 2 * β * b + β ^ 2 * ‖transportedDir R x p α k‖ ^ 2 := by
      rw [hrun.dir_succ k, ← hN, ← hN', ← hβ, norm_add_sq_real, norm_neg, hng, ← hN',
        inner_neg_left, real_inner_smul_right, hinner, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    have hTk := hT k
    have hT2 : ‖transportedDir R x p α k‖ ^ 2 ≤ ‖p k‖ ^ 2 := by
      have := norm_nonneg (transportedDir R x p α k)
      nlinarith
    rw [Finset.sum_range_succ]
    set S := ∑ j ∈ Finset.range (k + 1), (‖RiemOpt.BFGS.Df (E := E) f (x j)‖ ^ 2)⁻¹ with hS
    have e4 : ∀ k', ‖RiemOpt.BFGS.Df (E := E) f (x k')‖ ^ 4 =
        (‖RiemOpt.BFGS.Df (E := E) f (x k')‖ ^ 2) ^ 2 := fun k' => by ring
    rw [e4 k] at ih
    rw [e4 (k + 1), ← hN']
    rw [← hN] at ih
    -- assemble
    have hstep1 : ‖p (k + 1)‖ ^ 2 ≤ C * N' + β ^ 2 * ‖p k‖ ^ 2 := by
      rw [hexp]
      have h2 : -2 * β * b ≤ 2 * c₂ / (1 - c₂) * N' := by
        have := mul_le_mul_of_nonneg_left hbb hβ0
        rw [← hβN]
        have e : 2 * c₂ / (1 - c₂) * (β * N) = 2 * (β * (c₂ * (N / (1 - c₂)))) := by
          field_simp
        rw [e]
        linarith
      have h3 : β ^ 2 * ‖transportedDir R x p α k‖ ^ 2 ≤ β ^ 2 * ‖p k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hT2 (sq_nonneg β)
      have hCN : C * N' = N' + 2 * c₂ / (1 - c₂) * N' := by
        rw [hC]; field_simp; ring
      linarith
    have hstep2 : β ^ 2 * ‖p k‖ ^ 2 ≤ C * N' ^ 2 * S := by
      have := mul_le_mul_of_nonneg_left ih (sq_nonneg β)
      have e : β ^ 2 * (C * N ^ 2 * S) = C * N' ^ 2 * S := by rw [← hβN]; ring
      linarith
    have e5 : C * N' ^ 2 * (S + N'⁻¹) = C * N' ^ 2 * S + C * N' := by
      field_simp
    rw [e5]
    linarith
