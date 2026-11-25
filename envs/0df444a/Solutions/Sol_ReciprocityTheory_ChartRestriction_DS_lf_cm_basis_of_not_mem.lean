-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lf_cm_basis_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:54.632077+00:00
-- url     : https://prove2.me/submissions/d3b8e36d-ab51-4cf5-898f-46dd8ffdd3a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfa_basis_list
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfa_cm_list

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    cmFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_basis_list]
  apply lfa_cm_list
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  apply hx
  rw [← hi, Equiv.apply_symm_apply]
  exact Finset.orderEmbOfFin_mem S rfl i
end ReciprocityTheory.ChartRestriction.DS
