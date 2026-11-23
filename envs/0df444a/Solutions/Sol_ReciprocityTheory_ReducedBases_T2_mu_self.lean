-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.mu_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:03.627412+00:00
-- url     : https://prove2.me/submissions/d38d8ca1-5791-40c1-9e9a-f7babdae751a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_b_self
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero

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
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (k : Fin d) : mu b k k = 1 := by
  unfold mu
  rw [inner_gs_b_self, div_self]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (gs_ne_zero b hb k))
end ReciprocityTheory.ReducedBases.T2
