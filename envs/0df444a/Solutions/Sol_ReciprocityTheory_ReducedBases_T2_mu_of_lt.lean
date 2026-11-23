-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.mu_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:03.521635+00:00
-- url     : https://prove2.me/submissions/7449b696-d4de-42b6-a962-66e117110bdd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_inner_b_of_lt

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
theorem _root_.solution (b : Fin d → E) {i j : Fin d} (h : i < j) : mu b i j = 0 := by
  unfold mu
  rw [gs_inner_b_of_lt b h, zero_div]
end ReciprocityTheory.ReducedBases.T2
