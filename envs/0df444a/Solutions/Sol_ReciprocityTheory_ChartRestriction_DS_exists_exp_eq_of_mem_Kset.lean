-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exists_exp_eq_of_mem_Kset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:19.828141+00:00
-- url     : https://prove2.me/submissions/e34b5bf2-07eb-40e9-9874-0d34b4f5caeb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_inK_exp_eq_of_mem_Kset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k :=
  exists_inK_exp_eq_of_mem_Kset hk
end ReciprocityTheory.ChartRestriction.DS
