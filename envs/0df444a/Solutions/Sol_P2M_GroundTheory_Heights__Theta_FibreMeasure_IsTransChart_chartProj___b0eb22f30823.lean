-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_chartProj___b0eb22f30823
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:04:38.839264+00:00
-- url     : https://prove2.me/submissions/746bd416-cc56-4469-b749-f183f9124482

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
theorem _root_.solution (s : T) {X : G} (hX : X ∈ Ω) :
    chartProj Γ σ (σ s X) = chartProj Γ σ X := by
  have h := ‹IsTransChart _ _ _ _›
  unfold GroundTheory.Heights₂.Theta.FibreMeasure.chartProj
  rw [h.shift _ _ hX, h.add _ _ _ hX]
  congr 1
  abel



