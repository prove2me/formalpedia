-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfLift_mem_physSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:33.222312+00:00
-- url     : https://prove2.me/submissions/484dd297-3d28-4ae0-886a-87f03b8bb80c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_cm_basis_of_not_mem


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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (x : LfIdx ε → N) : lfLift ε x ∈ physicalSubspace (N := N) ε := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  simp only [lfLift, map_sum, cmT, TensorProduct.map_tmul, LinearMap.id_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  have hS : finProdFinEquiv (i, a) ∉ S.1 := by
    intro h
    have := S.2 h
    simp only [lfPhysModes, Finset.mem_filter, Equiv.symm_apply_apply] at this
    exact hia this.2
  rw [lf_cm_basis_of_not_mem (x := (i, a)) hS, TensorProduct.tmul_zero]
end ReciprocityTheory.ChartRestriction.DS
