-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Wm_perp_Wp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:57.229486+00:00
-- url     : https://prove2.me/submissions/00d36f91-61ce-42a6-8631-311ffb9da8ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_crossOp_eig_eq_zero

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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hU : IsInfUnitary ε E) {x y : Big n 1 M} (hx : x ∈ Wm ε E V)
    (hy : y ∈ Wp ε E V) : inner ℂ x y = 0 := by
  have h : (Wm ε E V).IsOrtho (Wp ε E V) := by
    unfold Wm Wp
    refine Submodule.isOrtho_iSup_left.mpr fun θ => Submodule.isOrtho_iSup_left.mpr fun hθ =>
      Submodule.isOrtho_iSup_right.mpr fun θ' => Submodule.isOrtho_iSup_right.mpr fun hθ' => ?_
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff] at hu hv
    exact inner_crossOp_eig_eq_zero hU (ne_of_lt (hθ.trans hθ')) hu.1 hv.1
  exact Submodule.isOrtho_iff_inner_eq.mp h x hx y hy
end ReciprocityTheory.ChartRestriction.DS
