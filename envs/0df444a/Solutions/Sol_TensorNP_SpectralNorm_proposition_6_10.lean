-- Prove2me | solution 1 for TensorNP.SpectralNorm.proposition_6_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T05:00:15.721521+00:00
-- url     : https://prove2.me/submissions/595cb269-f488-4021-8236-1f05dcd067c0

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TensorNP_SpectralNorm_Tensor

open scoped BigOperators
open Matrix Set Metric

namespace TensorPolarization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma diagonal_bound (B : E → E → F) (C : ℝ) (_hC : 0 ≤ C)
    (hzero : B 0 0 = 0)
    (hhom : ∀ (c : ℝ) (z : E), B (c • z) (c • z) = c ^ 2 • B z z)
    (hbound : ∀ z, ‖z‖ = 1 → ‖B z z‖ ≤ C) (z : E) :
    ‖B z z‖ ≤ C * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · simp [hz, hzero]
  · have hu : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hz]
    have hb : B z z = ‖z‖ ^ 2 • B ((‖z‖⁻¹ : ℝ) • z) ((‖z‖⁻¹ : ℝ) • z) := by
      simpa only [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul] using
        hhom ‖z‖ ((‖z‖⁻¹ : ℝ) • z)
    rw [hb, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound _ hu) (sq_nonneg ‖z‖)

lemma polarization_bound (B : E → E → F) (C : ℝ) (hC : 0 ≤ C)
    (hzero : B 0 0 = 0)
    (hhom : ∀ (c : ℝ) (z : E), B (c • z) (c • z) = c ^ 2 • B z z)
    (hpol : ∀ u v, (4 : ℝ) • B u v = B (u+v) (u+v) - B (u-v) (u-v))
    (hbound : ∀ z, ‖z‖ = 1 → ‖B z z‖ ≤ C)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖B u v‖ ≤ C := by
  have hp := norm_sub_le (B (u+v) (u+v)) (B (u-v) (u-v))
  rw [← hpol, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hp
  have hpar : ‖u+v‖ ^ 2 + ‖u-v‖ ^ 2 = 4 := by
    nlinarith [parallelogram_law_with_norm ℝ u v]
  have hdiag := add_le_add (diagonal_bound B C hC hzero hhom hbound (u+v))
    (diagonal_bound B C hC hzero hhom hbound (u-v))
  rw [← mul_add, hpar] at hdiag
  linarith
end TensorPolarization

namespace SymmetricProof

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def B {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (u v : E n) : E m :=
  WithLp.toLp 2 fun k => u ⬝ᵥ (A k *ᵥ v)

lemma norm_eq_l2 {n : ℕ} (u : E n) : ‖u‖ = TensorNP.SpectralNorm.l2norm u := by
  simpa [TensorNP.SpectralNorm.l2norm] using EuclideanSpace.norm_eq u

lemma norm_B_sq {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    ‖B A u v‖^2 = ∑ k, (u ⬝ᵥ (A k *ᵥ v))^2 := by
  exact EuclideanSpace.real_norm_sq_eq (B A u v)

lemma B_zero {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : B A 0 0 = 0 := by
  simp [B]
  rfl

lemma B_hom {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (z : E n) :
    B A (c • z) (c • z) = c^2 • B A z z := by
  ext k
  simp [B, mulVec_smul, smul_dotProduct, dotProduct_smul, pow_two, mul_assoc]

lemma symmetric_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (u v : Fin n → ℝ) : u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  simpa only [hM.eq] using Matrix.dotProduct_transpose_mulVec M u v

lemma B_polar {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, (A k).IsSymm) (u v : E n) :
    (4 : ℝ) • B A u v = B A (u+v) (u+v) - B A (u-v) (u-v) := by
  ext k
  change 4 * (u ⬝ᵥ (A k *ᵥ v)) =
    (u+v) ⬝ᵥ (A k *ᵥ (u+v)) - (u-v) ⬝ᵥ (A k *ᵥ (u-v))
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  rw [symmetric_dot (A k) (hA k) v u]
  ring

lemma continuous_diagonal {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun z : E n => ‖B A z z‖) := by
  unfold B
  fun_prop

lemma B_bound {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, (A k).IsSymm) (C : ℝ) (hC : 0 ≤ C)
    (hdiag : ∀ z : E n, ‖z‖ = 1 → ‖B A z z‖ ≤ C)
    (u v : E n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖B A u v‖ ≤ C := by
  exact TensorPolarization.polarization_bound (B A) C hC (B_zero A) (B_hom A)
    (B_polar A hA) hdiag u v hu hv

end SymmetricProof

open TensorNP.SpectralNorm SymmetricProof

theorem solution {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, (A k).IsSymm) :
    sSup {t : ℝ | ∃ u v : Fin n → ℝ, l2norm u = 1 ∧ l2norm v = 1 ∧
        t = ∑ k, (u ⬝ᵥ (A k *ᵥ v)) ^ 2} =
      sSup {t : ℝ | ∃ v : Fin n → ℝ, l2norm v = 1 ∧ t = ∑ k, (v ⬝ᵥ (A k *ᵥ v)) ^ 2} := by
  by_cases hn : n = 0
  · subst n
    simp [l2norm]
  · have : NeZero n := ⟨hn⟩
    have hne : (sphere (0 : E n) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : E n) 1).exists_isMaxOn hne (continuous_diagonal A).continuousOn
    have hyunit : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hbound (u v : Fin n → ℝ) (hu : l2norm u = 1) (hv : l2norm v = 1) :
        (∑ k, (u ⬝ᵥ (A k *ᵥ v))^2) ≤ ‖B A y y‖^2 := by
      have hnorm := B_bound A hA ‖B A y y‖ (norm_nonneg _)
        (fun z hz => hmax (mem_sphere_zero_iff_norm.mpr hz))
        (WithLp.toLp 2 u) (WithLp.toLp 2 v)
        (by simpa only [norm_eq_l2] using hu) (by simpa only [norm_eq_l2] using hv)
      simpa only [norm_B_sq] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
    have hy2 : l2norm y = 1 := (norm_eq_l2 y).symm.trans hyunit
    have hleft : IsGreatest {t : ℝ | ∃ u v : Fin n → ℝ, l2norm u = 1 ∧ l2norm v = 1 ∧
        t = ∑ k, (u ⬝ᵥ (A k *ᵥ v)) ^ 2} (‖B A y y‖^2) :=
      ⟨⟨y, y, hy2, hy2, norm_B_sq A y y⟩,
        fun t ⟨u, v, hu, hv, ht⟩ => ht.symm ▸ hbound u v hu hv⟩
    have hright : IsGreatest {t : ℝ | ∃ v : Fin n → ℝ, l2norm v = 1 ∧
        t = ∑ k, (v ⬝ᵥ (A k *ᵥ v)) ^ 2} (‖B A y y‖^2) :=
      ⟨⟨y, hy2, norm_B_sq A y y⟩,
        fun t ⟨v, hv, ht⟩ => ht.symm ▸ hbound v v hv hv⟩
    exact hleft.csSup_eq.trans hright.csSup_eq.symm
