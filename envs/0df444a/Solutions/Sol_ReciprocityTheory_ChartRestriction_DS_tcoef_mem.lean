-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tcoef_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:08.073659+00:00
-- url     : https://prove2.me/submissions/8a09cdc8-cf0b-418d-94e8-d73f1454f2f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_map_left

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
theorem _root_.solution {L : Submodule ℂ M} {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)))
    (φ : Module.Dual ℂ (Fock n)) : tcoef φ y ∈ L := by
  obtain ⟨z, rfl⟩ := hy
  rw [tcoef_map_left]
  exact (tcoef φ z).2
end ReciprocityTheory.ChartRestriction.DS
