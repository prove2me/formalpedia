-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P25.phaseOscillator_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:28:45.587643+00:00
-- url     : https://prove2.me/submissions/0f6c64b5-45c7-458a-83ad-45f5e83d4433

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25
noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

open QAlgorithms.Papers.Independent.Renew46.P25

lemma g64g_diffF {n : ℕ} (F : SchwartzMap (PhaseSpaceGrouped n) ℂ) :
    Differentiable ℝ (F : PhaseSpaceGrouped n → ℂ) := F.differentiable

lemma g64g_diffdF {n : ℕ} (F : SchwartzMap (PhaseSpaceGrouped n) ℂ) (v : PhaseSpaceGrouped n) :
    Differentiable ℝ (fun y => fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y v) := by
  have h : ContDiff ℝ 1 (fun y => fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y) :=
    (F.smooth ⊤).fderiv_right (by norm_cast)
  exact (h.clm_apply contDiff_const).differentiable (by norm_num)

lemma g64g_diffc {n : ℕ} (k : Phase n) :
    Differentiable ℝ (fun y : PhaseSpaceGrouped n => ((y k / 2 : ℝ) : ℂ)) := by
  have : (fun y : PhaseSpaceGrouped n => ((y k / 2 : ℝ) : ℂ)) =
      fun y => Complex.ofRealCLM ((1 / 2 : ℝ) • (EuclideanSpace.proj k : PhaseSpaceGrouped n →L[ℝ] ℝ) y) := by
    funext y; simp; ring
  rw [this]; fun_prop

lemma g64g_fderivc {n : ℕ} (k : Phase n) (z w : PhaseSpaceGrouped n) :
    fderiv ℝ (fun y : PhaseSpaceGrouped n => ((y k / 2 : ℝ) : ℂ)) z w = ((w k / 2 : ℝ) : ℂ) := by
  have : (fun y : PhaseSpaceGrouped n => ((y k / 2 : ℝ) : ℂ)) =
      fun y => (Complex.ofRealCLM.comp ((1 / 2 : ℝ) • (EuclideanSpace.proj k : PhaseSpaceGrouped n →L[ℝ] ℝ))) y := by
    funext y; simp; ring
  rw [this, ContinuousLinearMap.fderiv]
  simp; ring

lemma g64g_dB {n : ℕ} (F : SchwartzMap (PhaseSpaceGrouped n) ℂ) (k : Phase n)
    (v : PhaseSpaceGrouped n) (s : ℂ) (z w : PhaseSpaceGrouped n) :
    fderiv ℝ (fun y => ((y k / 2 : ℝ) : ℂ) * F y + s * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y v) z w =
      ((w k / 2 : ℝ) : ℂ) * F z + ((z k / 2 : ℝ) : ℂ) * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) z w +
        s * fderiv ℝ (fun y => fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y v) z w := by
  have h : HasFDerivAt (fun y : PhaseSpaceGrouped n => ((y k / 2 : ℝ) : ℂ) * F y +
      s * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y v) _ z := ((g64g_diffc k z).hasFDerivAt.mul (g64g_diffF F z).hasFDerivAt).add
    (((g64g_diffdF F v) z).hasFDerivAt.const_mul s)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, g64g_fderivc]
  ring

theorem solution (n : ℕ) (hn : 0 < n)
    (F : SchwartzMap (PhaseSpaceGrouped n) ℂ) (z : PhaseSpaceGrouped n) :
    phaseOscillator F z = -(1 / 2 : ℂ) * phaseLaplacian F z -
      (Complex.I / 2) * phaseAngularDerivative F z +
      (((∑ k : Phase n, z k ^ 2) / 8 : ℝ) : ℂ) * F z := by
  have eP : ∀ j : Fin n, groupedBoppPosition j (F : PhaseSpaceGrouped n → ℂ) =
      fun y => ((y (Sum.inl j) / 2 : ℝ) : ℂ) * F y +
        Complex.I * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y (EuclideanSpace.single (Sum.inr j) 1) := by
    intro j; funext y; rfl
  have eM : ∀ j : Fin n, groupedBoppMomentum j (F : PhaseSpaceGrouped n → ℂ) =
      fun y => ((y (Sum.inr j) / 2 : ℝ) : ℂ) * F y +
        (-Complex.I) * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y (EuclideanSpace.single (Sum.inl j) 1) := by
    intro j; funext y; simp only [groupedBoppMomentum]; ring
  unfold phaseOscillator phaseLaplacian phaseAngularDerivative
  simp only [Fintype.sum_sum_type]
  have hP : ∀ j : Fin n, groupedBoppPosition j (groupedBoppPosition j (F : PhaseSpaceGrouped n → ℂ)) z =
      ((z (Sum.inl j) / 2 : ℝ) : ℂ) * (((z (Sum.inl j) / 2 : ℝ) : ℂ) * F z +
        Complex.I * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) z (EuclideanSpace.single (Sum.inr j) 1)) +
      Complex.I * (((z (Sum.inl j) / 2 : ℝ) : ℂ) * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) z (EuclideanSpace.single (Sum.inr j) 1) +
        Complex.I * fderiv ℝ (fun y => fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y (EuclideanSpace.single (Sum.inr j) 1)) z
          (EuclideanSpace.single (Sum.inr j) 1)) := by
    intro j
    conv_lhs => rw [groupedBoppPosition, eP j, g64g_dB]
    simp
  have hM : ∀ j : Fin n, groupedBoppMomentum j (groupedBoppMomentum j (F : PhaseSpaceGrouped n → ℂ)) z =
      ((z (Sum.inr j) / 2 : ℝ) : ℂ) * (((z (Sum.inr j) / 2 : ℝ) : ℂ) * F z +
        (-Complex.I) * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) z (EuclideanSpace.single (Sum.inl j) 1)) -
      Complex.I * (((z (Sum.inr j) / 2 : ℝ) : ℂ) * fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) z (EuclideanSpace.single (Sum.inl j) 1) +
        (-Complex.I) * fderiv ℝ (fun y => fderiv ℝ (F : PhaseSpaceGrouped n → ℂ) y (EuclideanSpace.single (Sum.inl j) 1)) z
          (EuclideanSpace.single (Sum.inl j) 1)) := by
    intro j
    conv_lhs => rw [groupedBoppMomentum, eM j, g64g_dB]
    simp
  simp only [hP, hM]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring_nf
  rw [Complex.I_sq]
  ring
