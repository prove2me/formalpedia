-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.lift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:12.428093+00:00
-- url     : https://prove2.me/submissions/002bb9a9-dade-435a-a759-ac237d8952f7

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
theorem _root_.solution (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ * G₁) (F₂ * G₂) = lift F₁ F₂ * lift G₁ G₂ := LinearMap.ext fun _ => rfl
end ReciprocityTheory.ChartRestriction.DS.USum
