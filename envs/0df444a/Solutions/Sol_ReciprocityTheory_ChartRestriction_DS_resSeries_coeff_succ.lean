-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:51.229999+00:00
-- url     : https://prove2.me/submissions/82f9072a-502e-4462-bd32-e622ec8f12f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ__6d30f8d603e9

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
theorem _root_.solution {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) = ∑ s, resid a s * a s ^ k := by
  rw [resSeries_coeff_succ' ha k]
  rfl
end ReciprocityTheory.ChartRestriction.DS
