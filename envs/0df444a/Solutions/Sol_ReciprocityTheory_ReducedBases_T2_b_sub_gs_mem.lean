-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.b_sub_gs_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:22.784671+00:00
-- url     : https://prove2.me/submissions/0b15c4a4-9d17-48fe-8073-f9b5878908ef

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
theorem _root_.solution (b : Fin d → E) (k : Fin d) : b k - gs b k ∈ span ℝ (b '' Set.Iio k) := by
  rw [← span_gramSchmidt_Iio ℝ b k]
  have hdef := gramSchmidt_def ℝ b k
  have hrw : b k - gs b k = b k - gramSchmidt ℝ b k := rfl
  rw [hrw, hdef, sub_sub_cancel]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hsub : (ℝ ∙ gramSchmidt ℝ b i) ≤ span ℝ (gramSchmidt ℝ b '' Set.Iio k) := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩
  apply hsub
  first
    | exact Submodule.coe_mem _
    | exact Submodule.starProjection_apply_mem _ _
    | simp
end ReciprocityTheory.ReducedBases.T2
