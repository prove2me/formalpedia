-- Prove2me | solution 1 for SumProduct.cubeSection_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:27.27122+00:00
-- url     : https://prove2.me/submissions/23cf16e1-416c-4c47-8f10-7cba1f7d62bf

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.mem_cubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
namespace SumProduct
theorem _root_.solution (r : ℝ) (hr : 0 ≤ r) :
    cubeSection ι r = r • cubeSection ι 1 := by
  rcases hr.eq_or_lt with rfl | hr0
  · -- `r = 0`: both sides are `{0}`.
    have hne : (cubeSection ι 1).Nonempty := ⟨0, by simp [mem_cubeSection]⟩
    rw [Set.zero_smul_set hne]
    ext y
    simp only [mem_cubeSection, Set.mem_zero]
    constructor
    · rintro ⟨h1, -⟩
      funext i
      exact abs_eq_zero.mp (le_antisymm (h1 i) (abs_nonneg _))
    · rintro rfl
      refine ⟨fun i => ?_, ?_⟩ <;> simp
  · -- `0 < r`: rescale each coordinate by `r⁻¹`.
    have hr0' : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
    have key : ∀ a : ℝ, |r⁻¹ * a| ≤ 1 ↔ |a| ≤ r := fun a => by
      rw [abs_mul, abs_of_pos hr0', inv_mul_eq_div, div_le_one hr0]
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr0.ne', mem_cubeSection, mem_cubeSection]
    have hsum : (∑ i, (r⁻¹ • y) i) = r⁻¹ * ∑ i, y i := by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, key]; exact h1 i
      · rw [hsum, key]; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · have hi := h1 i; rw [Pi.smul_apply, smul_eq_mul, key] at hi; exact hi
      · rw [hsum, key] at h2; exact h2
end SumProduct
