-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.swap_gs_j
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:45.90274+00:00
-- url     : https://prove2.me/submissions/f56ad86e-a40d-4236-b811-f5f512b8c402

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_img
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_eq_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_inner_b_of_lt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_orth
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_b_self
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_span


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
    gs (b ∘ Equiv.swap j j1) j = gs b j1 + mu b j1 j • gs b j := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hne' : j1 ≠ j := fun h => hne h.symm
  have hsj : Equiv.swap j j1 j = j1 := Equiv.swap_apply_left j j1
  have hI : Set.Iio j1 = insert j (Set.Iio j) := by
    ext l
    simp only [Set.mem_Iio, Set.mem_insert_iff, Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  have hmem := b_sub_gs_mem b j1
  rw [hI, Set.image_insert_eq, Submodule.mem_span_insert] at hmem
  obtain ⟨c, s, hs, hcs⟩ := hmem
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hc : c = mu b j1 j := by
    have h1 : ⟪gs b j, b j1 - gs b j1⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
      rw [inner_sub_right, gs_orth b hne, sub_zero]
      unfold mu
      rw [div_mul_cancel₀ _ hG0]
    have h2 : ⟪gs b j, b j1 - gs b j1⟫_ℝ = c * ‖gs b j‖ ^ 2 := by
      rw [hcs, inner_add_right, real_inner_smul_right, inner_gs_b_self, inner_gs_span b j hs, add_zero]
    exact mul_right_cancel₀ hG0 (h2.symm.trans h1)
  subst hc
  refine gs_eq_of _ _ _ ?_ ?_
  · rw [swap_img b j j1 hj j hne]
    simp only [Function.comp_apply, hsj]
    have he : b j1 - (gs b j1 + mu b j1 j • gs b j) = mu b j1 j • (b j - gs b j) + s := by
      rw [sub_add_eq_sub_sub, hcs, smul_sub]
      abel
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (b_sub_gs_mem b j)) hs
  · intro i hi
    have hi1 : i < j1 := lt_trans hi (by rw [Fin.lt_iff_val_lt_val]; omega)
    have hsi : Equiv.swap j j1 i = i := Equiv.swap_apply_of_ne_of_ne (ne_of_lt hi) (ne_of_lt hi1)
    simp only [Function.comp_apply, hsi]
    rw [inner_add_left, real_inner_smul_left, gs_inner_b_of_lt b hi1, gs_inner_b_of_lt b hi]
    ring
end ReciprocityTheory.ReducedBases.T2
