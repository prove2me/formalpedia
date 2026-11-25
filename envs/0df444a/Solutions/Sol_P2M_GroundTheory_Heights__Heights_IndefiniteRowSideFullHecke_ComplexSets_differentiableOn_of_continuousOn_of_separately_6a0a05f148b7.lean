-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableOn_of_continuousOn_of_separately_6a0a05f148b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:34.110468+00:00
-- url     : https://prove2.me/submissions/eeb66c39-3c6b-4f67-b703-2352a0f819bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_continuousOn_of_separately_ff52795ca853

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    DifferentiableOn ℂ g U :=
  (analyticOnNhd_of_continuousOn_of_separately hU hc hs).differentiableOn
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
