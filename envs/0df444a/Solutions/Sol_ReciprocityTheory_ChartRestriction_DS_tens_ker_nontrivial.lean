-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tens_ker_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:01.038514+00:00
-- url     : https://prove2.me/submissions/feb9aaea-d2ae-4550-a2ae-0756e3b7fa4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_map_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_mem

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (T : Module.End ℂ M) {V : Submodule ℂ M} {x : TensorProduct ℂ M (Fock n)}
    (hx : x ∈ LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (hx0 : x ≠ 0) (hTx : TensorProduct.map T LinearMap.id x = 0) : ∃ v ∈ V, v ≠ 0 ∧ T v = 0 := by
  have hex : ∃ s, tcoef ((fockBasis n).coord s) x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx0
    rw [tcoef_expand x]
    simp [hcon]
  obtain ⟨s, hs⟩ := hex
  refine ⟨_, tcoef_mem hx _, hs, ?_⟩
  rw [← tcoef_map_left, hTx, map_zero]
end ReciprocityTheory.ChartRestriction.DS
