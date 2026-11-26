-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_____chartProj_83976a02a6f6
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:05:44.823841+00:00
-- url     : https://prove2.me/submissions/02c2db02-420a-4252-8de7-b76ea2480968

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
theorem _root_.solution {X : G} (hX : X ∈ Ω) : σ (Γ X) (chartProj Γ σ X) = X := by
  unfold GroundTheory.Heights₂.Theta.FibreMeasure.chartProj
  rw [(‹IsTransChart dX Γ Ω σ›).add _ _ _ hX, add_neg_cancel, (‹IsTransChart dX Γ Ω σ›).zero _ hX]



