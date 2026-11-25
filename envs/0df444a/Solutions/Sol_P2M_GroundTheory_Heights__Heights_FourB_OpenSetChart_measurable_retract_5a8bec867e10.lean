-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_measurable_retract_5a8bec867e10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:30.018347+00:00
-- url     : https://prove2.me/submissions/0c05f515-e622-496e-aad4-bbbf90bd83bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.FourB.OpenSetChart
variable {D : ℕ} {M : Set (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.FourB.OpenSetChart
theorem _root_.solution (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) :
    Measurable (retract x₀ hx₀) := by
  classical
  unfold retract
  exact (Measurable.ite hM.measurableSet measurable_id measurable_const).subtype_mk
end GroundTheory.Heights₂.Heights.FourB.OpenSetChart
