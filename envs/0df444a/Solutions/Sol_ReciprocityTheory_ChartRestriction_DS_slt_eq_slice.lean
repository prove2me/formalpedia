-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_eq_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:14.878898+00:00
-- url     : https://prove2.me/submissions/b0269a13-7c8f-4a15-bc80-e73cf75e1c94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slice_eq_slt

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
theorem _root_.solution {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (p : Fin n × Fin n)
    (A : Big n k M) : slt i r A = slice i ((slRest i).symm (p, r)) A := by
  simp only [slice_eq_slt, Equiv.apply_symm_apply]
end ReciprocityTheory.ChartRestriction.DS
