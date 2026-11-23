-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.sop_neg_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:33.02985+00:00
-- url     : https://prove2.me/submissions/87219916-3287-4a47-b2fc-64e6433bbc91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_sop_apply

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
theorem _root_.solution (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop 1 (-1) (sop A B x) = sop A B (sop 1 (-1) x) := by
  simp only [sop_apply, WithLp.ofLp_toLp]
  simp
end ReciprocityTheory.ChartRestriction.DS.USum
