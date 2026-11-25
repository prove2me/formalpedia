-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.actM_zM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:39.337976+00:00
-- url     : https://prove2.me/submissions/ff3fb826-21ad-465d-a148-4e2cf7d1f0b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_actM_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_actM_sub

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
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ} {ε : Fin n → Bool}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (zM a b c) = c • E a b - star c • E b a := by
  unfold zM
  rw [actM_sub, actM_single, actM_single]
end ReciprocityTheory.ChartRestriction.DS.USum
