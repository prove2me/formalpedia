-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.apply_mem_layer_succ_nc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:48.11497+00:00
-- url     : https://prove2.me/submissions/6ea0a4c0-3d64-4e8d-906d-07fa45de1c6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {a b : Fin n} (hab : ε a ≠ ε b) {k : ℕ} {v : M}
    (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by
  have h1 : (layer ε E V k).map (E a b) ≤ layer ε E V (k + 1) := by
    show _ ≤ layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
    exact le_sup_of_le_right (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)))
  exact h1 (Submodule.mem_map_of_mem hv)
end ReciprocityTheory.ChartRestriction.DS
