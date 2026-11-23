-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.swap_img
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:38.194864+00:00
-- url     : https://prove2.me/submissions/7371d7f7-635f-4937-b79a-ce502a18e74d

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_swap_lt

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
    (hk : k ≠ j1) : (b ∘ Equiv.swap j j1) '' Set.Iio k = b '' Set.Iio k := by
  have hs : (Equiv.swap j j1) '' Set.Iio k = Set.Iio k := by
    ext l
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact swap_lt j j1 hj k hk m hm
    · intro hl
      exact ⟨Equiv.swap j j1 l, swap_lt j j1 hj k hk l hl, Equiv.swap_apply_self _ _ _⟩
  rw [Set.image_comp, hs]
end ReciprocityTheory.ReducedBases.T2
