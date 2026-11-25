-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:37.512985+00:00
-- url     : https://prove2.me/submissions/c7557b6e-3252-4e32-b996-ae6cf59f93ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
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
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
theorem _root_.solution {k : ℕ} {O : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → ℂ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) : AnalyticOnNhd ℂ f O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hf.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ f (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hf.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
