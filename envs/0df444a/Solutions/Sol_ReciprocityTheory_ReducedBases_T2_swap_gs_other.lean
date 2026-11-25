-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.swap_gs_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:09.389796+00:00
-- url     : https://prove2.me/submissions/8187317a-a8a7-4981-883d-1e8f2ae35c2f

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_lt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_img
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_eq_of
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
theorem _root_.solution (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j) (hk1 : k ≠ j1) : gs (b ∘ Equiv.swap j j1) k = gs b k := by
  have hkk : Equiv.swap j j1 k = k := Equiv.swap_apply_of_ne_of_ne hk hk1
  refine gs_eq_of _ _ _ ?_ ?_
  · rw [swap_img b j j1 hj k hk1]
    simp only [Function.comp_apply, hkk]
    exact b_sub_gs_mem b k
  · intro i hi
    apply inner_gs_span b k
    apply Submodule.subset_span
    exact ⟨Equiv.swap j j1 i, swap_lt j j1 hj k hk1 i hi, rfl⟩
end ReciprocityTheory.ReducedBases.T2
