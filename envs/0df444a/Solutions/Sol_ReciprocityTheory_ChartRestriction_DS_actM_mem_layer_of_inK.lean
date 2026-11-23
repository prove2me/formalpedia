-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.actM_mem_layer_of_inK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:34.582063+00:00
-- url     : https://prove2.me/submissions/39c2dab3-5007-47aa-b2b6-3279939f6420

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_kStable


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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) :
    actM E Z x ∈ layer ε E V k := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h ⊢ <;>
      first | exact h | linear_combination h / 2 | linear_combination -h / 2
  rw [actM, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  by_cases hab : ε a = ε b
  · exact Submodule.smul_mem _ _ (layer_kStable hE hV k a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact zero_mem _
end ReciprocityTheory.ChartRestriction.DS
