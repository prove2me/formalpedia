-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.gs_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:46.628514+00:00
-- url     : https://prove2.me/submissions/dacbcad3-d1b5-4d9b-963e-e8a30a3be146

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
theorem _root_.solution (b : Fin d → E) {i j : Fin d} (h : i ≠ j) : ⟪gs b i, gs b j⟫_ℝ = 0 :=
  gramSchmidt_orthogonal ℝ b h
end ReciprocityTheory.ReducedBases.T2
