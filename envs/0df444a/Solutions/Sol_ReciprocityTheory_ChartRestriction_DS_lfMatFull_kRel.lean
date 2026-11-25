-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfMatFull_kRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:25.240241+00:00
-- url     : https://prove2.me/submissions/270f259d-39d7-4427-998a-84db64e1323e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isCAR_fock
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sgE_comm


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
theorem _root_.solution (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMatFull ε) := by
  intro a b c d hab hcd
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n))
    (sgE_comm isCAR_fock ε a b c d hab hcd)
  split_ifs at h ⊢ <;> simpa only [lfMatFull, map_sub, map_zero, LinearMap.toMatrix_mul] using h
end ReciprocityTheory.ChartRestriction.DS
