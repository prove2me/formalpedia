-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slRest_symm_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:06.991173+00:00
-- url     : https://prove2.me/submissions/1e805c2f-ae0e-4c8d-bc17-a65bf9f15b50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact

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
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n) :
    (slRest i).symm (p, r) i = p := by
  simp [slRest, Equiv.funSplitAt_symm_apply]
end ReciprocityTheory.ChartRestriction.DS
