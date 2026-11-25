-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.lift_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:08.812805+00:00
-- url     : https://prove2.me/submissions/5655f0e0-6660-40ad-9861-fa1d3c3f9f48

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
variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution : lift (0 : Module.End ℂ D₁) (0 : Module.End ℂ D₂) = 0 :=
  LinearMap.ext fun _ => rfl
end ReciprocityTheory.ChartRestriction.DS.USum
