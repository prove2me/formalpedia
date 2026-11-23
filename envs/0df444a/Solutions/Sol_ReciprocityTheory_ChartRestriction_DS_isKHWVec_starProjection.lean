-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isKHWVec_starProjection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:59.26166+00:00
-- url     : https://prove2.me/submissions/d0d6d189-d238-4ec9-9dba-5dd8d523a027

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hU : IsKUnitary ε E) {S : Submodule ℂ M}
    [S.HasOrthogonalProjection] (hS : IsKStableSub ε E S) {μ : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (S.starProjection w) := by
  have hcomm : ∀ a b, ε a = ε b → ∀ v, S.starProjection (E a b v) = E a b (S.starProjection v) := by
    intro a b hab v
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS a b hab _ (S.starProjection_apply_mem v))
    intro u hu
    rw [← map_sub, hU a b hab]
    exact Submodule.inner_left_of_mem_orthogonal (hS b a hab.symm u hu)
      (Submodule.sub_starProjection_mem_orthogonal v)
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hcomm a a rfl, hw.1 a, map_smul]
  · rw [← hcomm a b he, hw.2 a b hab he, map_zero]
end ReciprocityTheory.ChartRestriction.DS
