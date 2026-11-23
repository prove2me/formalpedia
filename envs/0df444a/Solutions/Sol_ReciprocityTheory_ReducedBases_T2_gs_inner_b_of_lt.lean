-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.gs_inner_b_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:11.771531+00:00
-- url     : https://prove2.me/submissions/ce1e141d-3bd1-4773-8a39-99f1d4f203da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt

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
theorem _root_.solution (b : Fin d → E) {i j : Fin d} (h : i < j) : ⟪gs b j, b i⟫_ℝ = 0 :=
  gramSchmidt_inv_triangular ℝ b h
end ReciprocityTheory.ReducedBases.T2
