-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_gram_trace_growth
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:48:58.53459+00:00
-- url     : https://prove2.me/submissions/e2864a60-0156-4c86-8bcd-75c4e7c1b251

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

set_option autoImplicit false

namespace CexE5bdf40d

open ShorNonsmooth.SpaceDilation

abbrev E2 := EuclideanSpace ℝ (Fin 2)

noncomputable def sw : E2 ≃ₗᵢ[ℝ] E2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

theorem sw_apply (v : E2) (i : Fin 2) : sw v i = v (Equiv.swap (0 : Fin 2) 1 i) := by
  simp [sw, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem sw_symm_apply (v : E2) (i : Fin 2) : sw.symm v i = v (Equiv.swap (0 : Fin 2) 1 i) := by
  simp [sw, LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]

theorem tr2 (f : E2 →ₗ[ℝ] E2) :
    LinearMap.trace ℝ E2 f =
      f (EuclideanSpace.single 0 1) 0 + f (EuclideanSpace.single 1 1) 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.trace, Fin.sum_univ_two]
  simp [LinearMap.toMatrix_apply]

noncomputable def B0 : E2 ≃L[ℝ] E2 := sw.toContinuousLinearEquiv

noncomputable def g0 : E2 → E2 := fun _ => EuclideanSpace.single 1 1

noncomputable def h0 : ℕ → E2 → E2 → ℝ := fun _ _ _ => 0

noncomputable def α0 : ℕ → ℝ := fun _ => 2

theorem gt0 : gTilde g0 h0 α0 0 B0 0 = EuclideanSpace.single 0 1 := by
  have hB : ((B0 : E2 ≃L[ℝ] E2) : E2 →L[ℝ] E2) = (sw : E2 →L[ℝ] E2) := rfl
  simp only [gTilde, sdg, hB, LinearIsometryEquiv.adjoint_eq_symm]
  ext i
  have := sw_symm_apply (g0 0) i
  fin_cases i <;> simp [g0] at this ⊢ <;> exact this

theorem A0_eq : (sdg g0 h0 α0 0 B0 0).A = (sw.symm : E2 →L[ℝ] E2) := rfl

theorem A0_apply (v : E2) (i : Fin 2) :
    (sdg g0 h0 α0 0 B0 0).A v i = v (Equiv.swap (0 : Fin 2) 1 i) := by
  rw [A0_eq]
  exact sw_symm_apply v i

theorem A1_eq : (sdg g0 h0 α0 0 B0 1).A =
    (dilation 2 (EuclideanSpace.single 0 1)).comp (sw.symm : E2 →L[ℝ] E2) := by
  have hg : ContinuousLinearMap.adjoint (sdg g0 h0 α0 0 B0 0).B (g0 (sdg g0 h0 α0 0 B0 0).x)
      = EuclideanSpace.single 0 1 := gt0
  show (sdgStep g0 h0 α0 0 (sdg g0 h0 α0 0 B0 0)).A = _
  rw [sdgStep, if_neg (by simp [g0])]
  simp only [hg, EuclideanSpace.norm_single, norm_one, inv_one, one_smul]
  rfl

theorem dil_apply (v : E2) (i : Fin 2) :
    dilation 2 (EuclideanSpace.single 0 1) v i =
      if i = 0 then 2 * v 0 else v i := by
  fin_cases i <;> simp [dilation, EuclideanSpace.inner_single_left]

theorem A1_apply0 (v : E2) : (sdg g0 h0 α0 0 B0 1).A v 0 = 2 * v 1 := by
  rw [A1_eq, ContinuousLinearMap.comp_apply, dil_apply]
  have := sw_symm_apply v 0
  simp at this ⊢
  rw [this]

theorem A1_apply1 (v : E2) : (sdg g0 h0 α0 0 B0 1).A v 1 = v 0 := by
  rw [A1_eq, ContinuousLinearMap.comp_apply, dil_apply]
  have := sw_symm_apply v 1
  simp at this ⊢
  rw [this]

theorem cex : ¬ (∀ {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 < a)
    (hα : ∀ j : ℕ, 1 ≤ j → α j = a)
    (hg : g (sdg g h α x₀ B₀ (k - 1)).x ≠ 0),
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((sdg g h α x₀ B₀ k).A.toLinearMap ∘ₗ (sdg g h α x₀ B₀ k).A.toLinearMap)
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          ((sdg g h α x₀ B₀ (k - 1)).A.toLinearMap ∘ₗ
            (sdg g h α x₀ B₀ (k - 1)).A.toLinearMap) +
        (a ^ 2 - 1) *
          ‖(sdg g h α x₀ B₀ (k - 1)).A
              (‖gTilde g h α x₀ B₀ (k - 1)‖⁻¹ •
                gTilde g h α x₀ B₀ (k - 1))‖ ^ 2) := by
  intro H
  have hx := H (n := 2) (by norm_num) g0 h0 α0 0 B0 1 le_rfl 2 (by norm_num)
    (fun _ _ => rfl) (by simp [g0])
  simp only [Nat.sub_self, gt0, EuclideanSpace.norm_single, norm_one, inv_one, one_smul] at hx
  rw [tr2, tr2] at hx
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, A1_apply0, A1_apply1,
    A0_apply] at hx
  have hn : ‖(sdg g0 h0 α0 0 B0 0).A (EuclideanSpace.single 0 1)‖ = 1 := by
    have : (sdg g0 h0 α0 0 B0 0).A (EuclideanSpace.single 0 1) = EuclideanSpace.single 1 1 := by
      ext i
      rw [A0_apply]
      fin_cases i <;> simp
    rw [this, EuclideanSpace.norm_single, norm_one]
  rw [hn] at hx
  simp at hx
  norm_num at hx

end CexE5bdf40d

open ShorNonsmooth.SpaceDilation in
theorem solution : ¬ (∀ {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 < a)
    (hα : ∀ j : ℕ, 1 ≤ j → α j = a)
    (hg : g (sdg g h α x₀ B₀ (k - 1)).x ≠ 0),
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((sdg g h α x₀ B₀ k).A.toLinearMap ∘ₗ (sdg g h α x₀ B₀ k).A.toLinearMap)
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          ((sdg g h α x₀ B₀ (k - 1)).A.toLinearMap ∘ₗ
            (sdg g h α x₀ B₀ (k - 1)).A.toLinearMap) +
        (a ^ 2 - 1) *
          ‖(sdg g h α x₀ B₀ (k - 1)).A
              (‖gTilde g h α x₀ B₀ (k - 1)‖⁻¹ •
                gTilde g h α x₀ B₀ (k - 1))‖ ^ 2) := by
  exact CexE5bdf40d.cex
