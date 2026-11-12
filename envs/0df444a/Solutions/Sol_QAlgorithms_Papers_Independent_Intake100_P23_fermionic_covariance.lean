-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P23.fermionic_covariance
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:56:48.397204+00:00
-- url     : https://prove2.me/submissions/391b9536-7caa-4ab0-bf5f-ffaffb2b81f4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section FermionicCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open QAlgorithms.Papers.Independent.Intake100.P23 in
theorem solution (phi : E → H →L[ℂ] H) (hphi : IsCAR phi)
    (v : H) (hq : FermionicQuasiFree phi v) :
    (∀ x y, inner ℂ v ((phi x * phi y) v) = (inner ℝ x y : ℂ) +
      (Complex.I / 2) * (carCovariance phi v x y : ℂ)) ∧
    (∀ x y, |carCovariance phi v x y| ≤ 2 * Real.sqrt |inner ℝ x x| * Real.sqrt |inner ℝ y y|) := by
  obtain ⟨_, _, hstar, hcar⟩ := hphi
  obtain ⟨hv1, _, _⟩ := hq
  have hvv : inner ℂ v v = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv1]
    norm_num
  have hsa : ∀ x (w u : H), inner ℂ w (phi x u) = inner ℂ (phi x w) u := by
    intro x w u
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hstar]
  have hab : ∀ x y, inner ℂ v ((phi x * phi y) v) = inner ℂ (phi x v) (phi y v) := by
    intro x y
    rw [ContinuousLinearMap.mul_apply, hsa]
  have hba : ∀ x y, inner ℂ v ((phi y * phi x) v) =
      (starRingEnd ℂ) (inner ℂ v ((phi x * phi y) v)) := by
    intro x y
    rw [hab, hab, inner_conj_symm]
  have hsum : ∀ x y, inner ℂ v ((phi x * phi y) v) + inner ℂ v ((phi y * phi x) v) =
      2 * (inner ℝ x y : ℂ) := by
    intro x y
    rw [← inner_add_right, ← ContinuousLinearMap.add_apply, hcar x y,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right, hvv,
      mul_one]
  have hc : ∀ x y, carCovariance phi v x y = 2 * (inner ℂ v ((phi x * phi y) v)).im := by
    intro x y
    unfold carCovariance
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, hba x y, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hre : ∀ x y, (inner ℂ v ((phi x * phi y) v)).re = inner ℝ x y := by
    intro x y
    have h := congrArg Complex.re (hsum x y)
    rw [hba x y, Complex.add_re, Complex.conj_re,
      show (2 : ℂ) * (inner ℝ x y : ℂ) = ((2 * inner ℝ x y : ℝ) : ℂ) by norm_num,
      Complex.ofReal_re] at h
    linarith
  have hnorm : ∀ x, ‖phi x v‖ = Real.sqrt |inner ℝ x x| := by
    intro x
    have h2 : inner ℂ v ((phi x * phi x) v) = (inner ℝ x x : ℂ) := by
      have := hsum x x
      linear_combination this / 2
    have h3 : ‖phi x v‖ ^ 2 = inner ℝ x x := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← hab, h2]
      exact Complex.ofReal_re _
    rw [← h3, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  refine ⟨?_, ?_⟩
  · intro x y
    rw [hc x y]
    have e : (Complex.I / 2) * (((2 * (inner ℂ v ((phi x * phi y) v)).im : ℝ)) : ℂ) =
        (((inner ℂ v ((phi x * phi y) v)).im : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, ← hre x y]
    exact (Complex.re_add_im _).symm
  · intro x y
    have h4 : |(inner ℂ v ((phi x * phi y) v)).im| ≤ ‖inner ℂ v ((phi x * phi y) v)‖ :=
      Complex.abs_im_le_norm _
    have h5 : ‖inner ℂ v ((phi x * phi y) v)‖ ≤ ‖phi x v‖ * ‖phi y v‖ := by
      rw [hab]
      exact norm_inner_le_norm _ _
    rw [hc x y, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), ← hnorm x, ← hnorm y]
    linarith

end FermionicCovariance

end
