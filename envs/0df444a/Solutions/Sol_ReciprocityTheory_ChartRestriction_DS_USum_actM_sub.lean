-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.actM_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:59.800331+00:00
-- url     : https://prove2.me/submissions/e557f365-c06f-4e69-9976-786378f4ffe1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X - Y) = actM E X - actM E Y := by
  unfold actM
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
end ReciprocityTheory.ChartRestriction.DS.USum
