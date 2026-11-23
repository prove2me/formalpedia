-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.apply_mem_noncompactLayer_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:34.472747+00:00
-- url     : https://prove2.me/submissions/f9803380-5293-4ede-8443-c170d4defd2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule

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
theorem _root_.solution {k : ℕ} {a b : Fin n} (hab : ε a ≠ ε b) {w : M}
    (hw : w ∈ layer ε E V k) : E a b w ∈ layer ε E V (k + 1) := by
  show E a b w ∈ layer ε E V k ⊔
    ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
  refine Submodule.mem_sup_right ?_
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem hab (Submodule.mem_map_of_mem hw)))
end ReciprocityTheory.ChartRestriction.DS
