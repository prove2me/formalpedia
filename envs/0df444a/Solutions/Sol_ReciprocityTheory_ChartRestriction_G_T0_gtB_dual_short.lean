-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtB_dual_short
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:18.012009+00:00
-- url     : https://prove2.me/submissions/2597d764-4f76-4228-bb74-7f72111c56cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_mink_pi_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_mink_pi_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_norm_le_sqrt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtB_inner_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtB_nondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) ∧
      ‖y‖ ≤ n / lam := by
  set e := EuclideanSpace.equiv (Fin n) ℝ with he
  set B := b.map e.toLinearEquiv with hBdef
  have hB : ∀ j, B j = e (b j) := fun j => by simp [B]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hdet : (lam / Real.sqrt n) ^ n ≤ |(Matrix.of B).det| := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_lt B (by positivity) hlt
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
    have hex : e (∑ i, c i • b i) = ∑ i, c i • B i := by simp [hB, map_sum, map_zsmul]
    have hx'0 : (∑ i, c i • b i) ≠ 0 := by intro h; apply hx0; rw [← hex, h, map_zero]
    have h1 := hmin _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hx'0
    have h2 := gtA_norm_le_sqrt_mul n (∑ i, c i • b i)
    rw [hex] at h2
    have : Real.sqrt n * ‖∑ i, c i • B i‖ < lam := by
      calc _ < Real.sqrt n * (lam / Real.sqrt n) := mul_lt_mul_of_pos_left hxn hsq
        _ = lam := by field_simp
    linarith
  set c := LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (gtB_nondeg n) b with hcdef
  have hc : ∀ i j, inner ℝ (c i) (b j) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left (gtB_nondeg n) b i j
    simpa using this
  set C := c.map e.toLinearEquiv with hCdef
  have hC : ∀ j, C j = e (c j) := fun j => by simp [C]
  have hCB : Matrix.of C * (Matrix.of B).transpose = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, hB, hC]
    rw [← gtB_inner_eq, hc]
    simp [eq_comm]
  have hdetCB : (Matrix.of C).det * (Matrix.of B).det = 1 := by
    rw [← Matrix.det_transpose (Matrix.of B), ← Matrix.det_mul, hCB, Matrix.det_one]
  have hdetC : |(Matrix.of C).det| ≤ (Real.sqrt n / lam) ^ n := by
    have hpos : 0 < (lam / Real.sqrt n) ^ n := by positivity
    have h1 : |(Matrix.of C).det| * |(Matrix.of B).det| = 1 := by rw [← abs_mul, hdetCB, abs_one]
    have h2 : |(Matrix.of C).det| = |(Matrix.of B).det|⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, show (Real.sqrt n / lam) ^ n = ((lam / Real.sqrt n) ^ n)⁻¹ by
      rw [← inv_pow, inv_div]]
    exact inv_anti₀ hpos hdet
  obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_le hn C (by positivity) hdetC
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
  have hex : e (∑ i, k i • c i) = ∑ i, k i • C i := by simp [hC, map_sum, map_zsmul]
  refine ⟨∑ i, k i • c i, ?_, ?_, ?_⟩
  · intro h; apply hx0; rw [← hex, h, map_zero]
  · intro j
    refine ⟨k j, ?_⟩
    rw [sum_inner]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]
    simp
  · have h2 := gtA_norm_le_sqrt_mul n (∑ i, k i • c i)
    rw [hex] at h2
    calc _ ≤ _ := h2
      _ ≤ Real.sqrt n * (Real.sqrt n / lam) := mul_le_mul_of_nonneg_left hxn hsq.le
      _ = n / lam := by
        rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
end ReciprocityTheory.ChartRestriction.G.T0
