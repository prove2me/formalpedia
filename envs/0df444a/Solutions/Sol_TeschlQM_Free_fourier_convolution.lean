-- Prove2me | solution 1 for TeschlQM.Free.fourier_convolution
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:56:53.685353+00:00
-- url     : https://prove2.me/submissions/e4d5b0fd-1017-4e4a-a7ce-82151e2c9cd2

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

open MeasureTheory Filter Topology FourierTransform Convolution
open scoped InnerProductSpace

namespace FCAux

theorem fourier_eq_mathlib {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    ∫ x : EuclideanSpace ℝ (Fin n), Complex.exp (-(⟪p, x⟫_ℝ : ℂ) * Complex.I) * f x
      = 𝓕 f ((2 * Real.pi)⁻¹ • p) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  rw [inner_smul_right, real_inner_comm]
  have : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem fourier_eq_scaled {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    TeschlQM.Free.fourier n f p
      = (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ * 𝓕 f ((2 * Real.pi)⁻¹ • p) := by
  unfold TeschlQM.Free.fourier
  rw [fourier_eq_mathlib]

/-- The platform's convolution is Mathlib's convolution for complex multiplication. -/
theorem conv_eq {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ) :
    (fun x => ∫ y, f y * g (x - y)) = f ⋆[ContinuousLinearMap.mul ℂ ℂ] g := rfl

theorem conv_comm_integral {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫ y, f y * g (x - y) = ∫ y, f (x - y) * g y := by
  rw [← integral_sub_left_eq_self (fun y => f y * g (x - y)) volume x]
  simp only [sub_sub_cancel]

theorem conv_integrable {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x => ∫ y, f y * g (x - y)) volume := by
  rw [conv_eq]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

theorem conv_young {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    ∫ x, ‖∫ y, f y * g (x - y)‖ ≤ (∫ x, ‖f x‖) * ∫ x, ‖g x‖ := by
  have hc := (conv_integrable f g hf hg).norm
  have hnf : Integrable (fun x => ‖f x‖) volume := hf.norm
  have hng : Integrable (fun x => ‖g x‖) volume := hg.norm
  have hc2 : Integrable ((fun x => ‖f x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun x => ‖g x‖)) volume :=
    hnf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hng
  have key := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hnf hng
  calc ∫ x, ‖∫ y, f y * g (x - y)‖
      ≤ ∫ x, ((fun x => ‖f x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun x => ‖g x‖)) x := by
        refine integral_mono hc hc2 fun x => ?_
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp [convolution_def]
    _ = (∫ x, ‖f x‖) * ∫ x, ‖g x‖ := by
        rw [key]; simp

theorem conv_fourier {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    TeschlQM.Free.fourier n (fun x => ∫ y, f y * g (x - y)) =
      fun p => (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * TeschlQM.Free.fourier n f p *
        TeschlQM.Free.fourier n g p := by
  funext p
  have hc : (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
    exact_mod_cast this.ne'
  rw [fourier_eq_scaled, fourier_eq_scaled, fourier_eq_scaled, conv_eq,
    Real.fourier_mul_convolution_eq hf hg]
  field_simp

end FCAux

/-- Teschl, Lemma 7.7: convolution of `L¹` functions. -/
theorem solution (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∀ x, ∫ y, f y * g (x - y) = ∫ y, f (x - y) * g y) ∧
      Integrable (fun x => ∫ y, f y * g (x - y)) volume ∧
      ∫ x, ‖∫ y, f y * g (x - y)‖ ≤ (∫ x, ‖f x‖) * ∫ x, ‖g x‖ ∧
      TeschlQM.Free.fourier n (fun x => ∫ y, f y * g (x - y)) =
        fun p => (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * TeschlQM.Free.fourier n f p *
          TeschlQM.Free.fourier n g p :=
  ⟨FCAux.conv_comm_integral f g, FCAux.conv_integrable f g hf hg, FCAux.conv_young f g hf hg,
    FCAux.conv_fourier f g hf hg⟩
