-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.inner_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:15.208803+00:00
-- url     : https://prove2.me/submissions/c49e7265-3fda-424f-ae69-2fe60f603dc2

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
theorem _root_.solution (x y : WithLp 2 (H₁ × H₂)) :
    inner ℂ x y = inner ℂ (ofLp x).1 (ofLp y).1 + inner ℂ (ofLp x).2 (ofLp y).2 := rfl
end ReciprocityTheory.ChartRestriction.DS.USum
