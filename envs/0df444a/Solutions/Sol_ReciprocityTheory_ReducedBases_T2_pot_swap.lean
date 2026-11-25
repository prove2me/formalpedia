-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.pot_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:11.70286+00:00
-- url     : https://prove2.me/submissions/3943db27-6e82-4a9d-903b-ba99231b72c4

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_gs_other
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_gs_j
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_gso_comp_swap_right_sq_mul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
private lemma prod_filter_le_ite_eq_of_mul_eq_one (j j1 : Fin d) (hj : j1.val = j.val + 1) (A B : ℝ) (hAB : A * B = 1)
    (k : Fin d) :
    ∏ i ∈ univ.filter (fun i : Fin d => i ≤ k),
        ((if i = j then A else 1) * (if i = j1 then B else 1)) = if k = j then A else 1 := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy k j with h | h | h
  · have h1 : ¬ j ≤ k := not_le.mpr h
    have h2 : ¬ j1 ≤ k := by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_neg h1, if_neg h2, if_neg (ne_of_lt h), one_mul]
  · have h2 : ¬ j1 ≤ j := by rw [Fin.le_iff_val_le_val]; omega
    rw [h, if_pos le_rfl, if_neg h2, if_pos rfl, mul_one]
  · have h1 : j ≤ k := le_of_lt h
    have h2 : j1 ≤ k := by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_pos h1, if_pos h2, if_neg (ne_of_gt h), hAB]
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    pot (b ∘ Equiv.swap j j1) =
      pot b * (‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2) := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hb' : LinearIndependent ℝ (b ∘ Equiv.swap j j1) := hb.comp _ (Equiv.injective _)
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hU0 : ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 ≠ 0 := by
    rw [← swap_gs_j b hb j j1 hj]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero _ hb' j))
  have hf : ∀ i, ‖gs (b ∘ Equiv.swap j j1) i‖ ^ 2 =
      ‖gs b i‖ ^ 2 * ((if i = j then ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 else 1) *
        (if i = j1 then ‖gs b j‖ ^ 2 / ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 else 1)) := by
    intro i
    by_cases h1 : i = j
    · rw [h1, if_pos rfl, if_neg hne, swap_gs_j b hb j j1 hj, mul_one, mul_comm,
        div_mul_cancel₀ _ hG0]
    · by_cases h2 : i = j1
      · rw [h2, if_neg (Ne.symm hne), if_pos rfl, one_mul, mul_div_assoc', eq_div_iff hU0]
        linear_combination norm_gso_comp_swap_right_sq_mul b hb j j1 hj
      · rw [if_neg h1, if_neg h2, swap_gs_other b j j1 hj i h1 h2]
        ring
  have hAB : ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 *
      (‖gs b j‖ ^ 2 / ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2) = 1 := by
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hG0 hU0)]
    ring
  have hk : ∀ k : Fin d, ∏ i ∈ univ.filter (fun i : Fin d => i ≤ k),
      ‖gs (b ∘ Equiv.swap j j1) i‖ ^ 2 =
      (∏ i ∈ univ.filter (fun i : Fin d => i ≤ k), ‖gs b i‖ ^ 2) *
        (if k = j then ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 else 1) := by
    intro k
    rw [← prod_filter_le_ite_eq_of_mul_eq_one j j1 hj _ _ hAB k, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hf i)
  unfold pot
  rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_ite_eq' univ j,
    if_pos (Finset.mem_univ j)]
end ReciprocityTheory.ReducedBases.T2
