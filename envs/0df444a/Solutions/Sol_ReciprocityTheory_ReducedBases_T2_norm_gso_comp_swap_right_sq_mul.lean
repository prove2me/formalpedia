-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.norm_gso_comp_swap_right_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:58.818918+00:00
-- url     : https://prove2.me/submissions/14dc58e5-67f5-4bf7-b462-89e7aa262646

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_img
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_gs_j
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_swap_j
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_eq_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_inner_b_of_lt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_orth
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_b_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    ‖gs (b ∘ Equiv.swap j j1) j1‖ ^ 2 * ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 =
      ‖gs b j‖ ^ 2 * ‖gs b j1‖ ^ 2 := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hjlt : j < j1 := by rw [Fin.lt_iff_val_lt_val]; omega
  have hb' : LinearIndependent ℝ (b ∘ Equiv.swap j j1) := hb.comp _ (Equiv.injective _)
  have hu := swap_gs_j b hb j j1 hj
  have hN := norm_swap_j b j j1 hj
  have hN0 : ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero _ hb' j))
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hv : gs (b ∘ Equiv.swap j j1) j1 = gs b j -
      (mu b j1 j * ‖gs b j‖ ^ 2 / ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2) • gs (b ∘ Equiv.swap j j1) j := by
    refine gs_eq_of _ _ _ ?_ ?_
    · have hmono : span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j) ≤
          span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hjlt)))
      have hbj : (b ∘ Equiv.swap j j1) j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) :=
        Submodule.subset_span ⟨j, hjlt, rfl⟩
      have hgs : gs (b ∘ Equiv.swap j j1) j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) := by
        have h := Submodule.sub_mem _ hbj (hmono (b_sub_gs_mem (b ∘ Equiv.swap j j1) j))
        rwa [sub_sub_cancel] at h
      have hB : b j - gs b j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) := by
        apply hmono
        rw [swap_img b j j1 hj j hne]
        exact b_sub_gs_mem b j
      have hbj1 : (b ∘ Equiv.swap j j1) j1 = b j := by simp [Equiv.swap_apply_right]
      rw [hbj1]
      have he : ∀ (t : ℝ) (x : E), b j - (gs b j - t • x) = (b j - gs b j) + t • x := by
        intro t x; abel
      rw [he]
      exact Submodule.add_mem _ hB (Submodule.smul_mem _ _ hgs)
    · intro i hi
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at hi; omega
      rcases lt_or_eq_of_le hij with h | h
      · have hsi : Equiv.swap j j1 i = i :=
          Equiv.swap_apply_of_ne_of_ne (ne_of_lt h) (ne_of_lt (lt_trans h hjlt))
        rw [inner_sub_left, real_inner_smul_left, gs_inner_b_of_lt _ h]
        simp only [Function.comp_apply, hsi, gs_inner_b_of_lt b h]
        ring
      · rw [h, inner_sub_left, real_inner_smul_left, inner_gs_b_self (b ∘ Equiv.swap j j1) j]
        have hsj : (b ∘ Equiv.swap j j1) j = b j1 := by simp
        have hmu : ⟪gs b j, b j1⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
          unfold mu
          rw [div_mul_cancel₀ _ hG0]
        rw [hsj, hmu, div_mul_cancel₀ _ hN0, sub_self]
  have hip : ⟪gs b j, gs (b ∘ Equiv.swap j j1) j⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
    rw [hu, inner_add_right, real_inner_smul_right, gs_orth b hne, real_inner_self_eq_norm_sq]
    ring
  have hN' : ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by
    rw [hu, hN]
  rw [hv, ← hu, norm_sub_sq_real, real_inner_smul_right, hip, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hN']
  have hD : ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 ≠ 0 := hN' ▸ hN0
  have key : mu b j1 j * ‖gs b j‖ ^ 2 / (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) *
      (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) = mu b j1 j * ‖gs b j‖ ^ 2 :=
    div_mul_cancel₀ _ hD
  linear_combination (mu b j1 j * ‖gs b j‖ ^ 2 / (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) *
      (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) - mu b j1 j * ‖gs b j‖ ^ 2) * key
end ReciprocityTheory.ReducedBases.T2
