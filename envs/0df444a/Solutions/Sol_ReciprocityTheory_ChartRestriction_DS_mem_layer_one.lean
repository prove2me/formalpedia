-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mem_layer_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:52.376264+00:00
-- url     : https://prove2.me/submissions/ffbd88ae-fbb0-41ac-86a4-5766861640cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB

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
theorem _root_.solution {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
    {v : M} (hv : v ∈ V) {a b : Fin n} (h : ε a ≠ ε b) : E a b v ∈ layer ε E V 1 := by
  show E a b v ∈ layer ε E V 0 ⊔
    ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V 0).map (E a b)
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem h ?_))
  exact Submodule.mem_map_of_mem hv
end ReciprocityTheory.ChartRestriction.DS
