-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P39.perfectCorrelationDissipator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:13:08.627917+00:00
-- url     : https://prove2.me/submissions/658c4ace-d568-4507-8a0c-c25e2357c3b2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39
noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

theorem s109_pcd_sum {n : ℕ} (D : ExcitonData n) (omega : ℝ) :
    ∑ m, siteTransition D m omega = if omega = 0 then (1 : SiteMatrix n) else 0 := by
  have hU : (D.basisChange : SiteMatrix n)ᴴ * (D.basisChange : SiteMatrix n) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 D.basisChange.2
  ext a b
  rw [Matrix.sum_apply]
  simp only [siteTransition]
  have hUab := congrFun (congrFun hU a) b
  rw [Matrix.mul_apply] at hUab
  simp only [Matrix.conjTranspose_apply] at hUab
  by_cases h : D.energy a - D.energy b = D.hbar * omega
  · simp only [h, if_true]
    rw [hUab]
    by_cases hab : a = b
    · subst hab
      have hw : omega = 0 := by
        have := D.hbar_positive
        rcases mul_eq_zero.1 (by linarith : D.hbar * omega = 0) with h1 | h1
        · linarith
        · exact h1
      simp [hw]
    · split_ifs <;> simp [Matrix.one_apply, hab]
  · simp only [h, if_false, Finset.sum_const_zero]
    split_ifs with hw
    · have hab : a ≠ b := by
        rintro rfl; apply h; simp [hw]
      simp [Matrix.one_apply, hab]
    · simp

theorem s109_pcd_factor {n : ℕ} (A : Fin n → SiteMatrix n) (c : ℂ) (X : SiteMatrix n) :
    ∑ m, ∑ k, c • (A m * X * (A k)ᴴ - (1 / 2 : ℂ) • (A m * (A k)ᴴ * X + X * A m * (A k)ᴴ)) =
      c • ((∑ m, A m) * X * (∑ k, A k)ᴴ - (1 / 2 : ℂ) •
        ((∑ m, A m) * (∑ k, A k)ᴴ * X + X * (∑ m, A m) * (∑ k, A k)ᴴ)) := by
  conv_lhs => rw [Finset.sum_comm]
  simp only [Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_sub,
    smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem s109_perfectCorrelationDissipator {n : ℕ} (D : ExcitonData n) (g : ℝ → ℝ)
    (hrates : ∀ omega, 0 ≤ g omega) :
    (∀ omega, ∑ m, siteTransition D m omega =
      if omega = 0 then (1 : SiteMatrix n) else 0) ∧
    (∀ omega X, printedPhononAt D (fun _ _ => 1) g omega X = 0) ∧
    (∀ X, printedPhonon D (fun _ _ => 1) g X = 0) := by
  have h2 : ∀ omega X, printedPhononAt D (fun _ _ => 1) g omega X = 0 := by
    intro omega X
    unfold printedPhononAt
    simp only [Complex.ofReal_one, mul_one]
    rw [s109_pcd_factor (fun m => siteTransition D m omega) (g omega : ℂ) X, s109_pcd_sum]
    split_ifs
    · simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
      rw [← two_smul ℂ X, smul_smul]; norm_num
    · simp
  refine ⟨s109_pcd_sum D, h2, ?_⟩
  intro X
  unfold printedPhonon
  exact Finset.sum_eq_zero (fun omega _ => h2 omega X)

end QAlgorithms.Papers.Independent.Advance50.P39

open QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n : ℕ} (D : ExcitonData n) (g : ℝ → ℝ)
    (hrates : ∀ omega, 0 ≤ g omega) :
    (∀ omega, ∑ m, siteTransition D m omega =
      if omega = 0 then (1 : SiteMatrix n) else 0) ∧
    (∀ omega X, printedPhononAt D (fun _ _ => 1) g omega X = 0) ∧
    (∀ X, printedPhonon D (fun _ _ => 1) g X = 0) :=
  s109_perfectCorrelationDissipator D g hrates

end
