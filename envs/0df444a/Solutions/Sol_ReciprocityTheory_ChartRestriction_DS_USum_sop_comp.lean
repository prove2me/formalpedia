-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.sop_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:33.472077+00:00
-- url     : https://prove2.me/submissions/2f5cde1b-0dd6-4a7d-a419-23b2968108c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution (A A' : H₁ →L[ℂ] H₁) (B B' : H₂ →L[ℂ] H₂) :
    sop (A.comp A') (B.comp B') = (sop A B).comp (sop A' B') := by
  ext x; rfl
end ReciprocityTheory.ChartRestriction.DS.USum
