-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.swap_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:18.794976+00:00
-- url     : https://prove2.me/submissions/e0349af9-7e88-46c2-bf44-2c311f5148fe

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul

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
theorem _root_.solution (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d) (hk : k ≠ j1) (l : Fin d)
    (hl : l < k) : Equiv.swap j j1 l < k := by
  by_cases h1 : l = j
  · rw [h1, Equiv.swap_apply_left]
    rw [h1] at hl
    have : k.val ≠ j1.val := fun h => hk (Fin.ext h)
    rw [Fin.lt_iff_val_lt_val] at hl ⊢
    omega
  · by_cases h2 : l = j1
    · rw [h2, Equiv.swap_apply_right]
      rw [h2] at hl
      rw [Fin.lt_iff_val_lt_val] at hl ⊢
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hl
end ReciprocityTheory.ReducedBases.T2
