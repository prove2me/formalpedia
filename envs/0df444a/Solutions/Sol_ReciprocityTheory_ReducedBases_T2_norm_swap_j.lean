-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.norm_swap_j
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:18.889365+00:00
-- url     : https://prove2.me/submissions/b1247e57-8d3c-4cf8-9c29-7073aab92903

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_orth


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
theorem _root_.solution (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) :
    ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by
  have hne : j1 ≠ j := fun h => by rw [Fin.ext_iff] at h; omega
  rw [norm_add_sq_real, real_inner_smul_right, gs_orth b hne, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring
end ReciprocityTheory.ReducedBases.T2
