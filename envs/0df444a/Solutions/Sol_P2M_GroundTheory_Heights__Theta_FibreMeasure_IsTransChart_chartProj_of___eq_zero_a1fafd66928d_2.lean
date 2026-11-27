-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_chartProj_of___eq_zero_a1fafd66928d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:12.97638+00:00
-- url     : https://prove2.me/submissions/e5eb8cae-8e84-4700-bace-5618f598ed7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_ContinuousOnChartProjM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FibreMeasure
open MeasureTheory Topology Filter Set
variable {G T : Type*}
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
  [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
variable {dX : Measure G} {Γ : G → T} {Ω : Set G} {σ : T → G → G}
open GroundTheory.Heights₂.Theta.FibreMeasure.IsTransChart
variable (h : IsTransChart dX Γ Ω σ)
include h
namespace GroundTheory.Heights₂.Theta.FibreMeasure.IsTransChart
theorem _root_.solution {X : G} (hX : X ∈ Ω) (h0 : Γ X = 0) : chartProj Γ σ X = X := by
  rw [chartProj, h0, neg_zero, h.zero _ hX]
end GroundTheory.Heights₂.Theta.FibreMeasure.IsTransChart
