-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuousOn_source_of_chart_59202810ddfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:36.655781+00:00
-- url     : https://prove2.me/submissions/9b09bad9-cbcb-4e90-ab02-340a9e7e1b98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {E : Type*} [TopologicalSpace E] {f : X → E} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by
  have h := hf.comp (A.chart j).continuousOn (fun y hy =>
    ⟨(A.chart j).map_source hy, by simpa [(A.chart j).left_inv hy] using hy⟩)
  exact h.congr (fun y hy => by simp [(A.chart j).left_inv hy])
end GroundTheory.Heights₂.Heights.HilbertSamuel
