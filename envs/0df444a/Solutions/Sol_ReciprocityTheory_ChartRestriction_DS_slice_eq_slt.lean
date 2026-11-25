-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slice_eq_slt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:57.491975+00:00
-- url     : https://prove2.me/submissions/50954adf-2e77-4fbb-b4e1-9321155f6b55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_update_eq_slRest

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
theorem _root_.solution {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (A : Big n k M) :
    slice i κ A = slt i (slRest i κ).2 A := by
  simp only [slice, slt, update_eq_slRest]
end ReciprocityTheory.ChartRestriction.DS
