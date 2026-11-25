-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NonIsolatedFibreCurve_analyticOnNhd_of_differentiableOn_c00fe3584ee6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:27.594447+00:00
-- url     : https://prove2.me/submissions/6f301757-c0bc-4303-a41a-f35bbc7dca81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNonIsolatedFibreCurve
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
open Topology Metric Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NonIsolatedFibreCurve
theorem _root_.solution {k : ℕ} {O : Set (Fin k → ℂ)}
    {g : (Fin k → ℂ) → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) : AnalyticOnNhd ℂ g O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ g (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hg.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt
end NonIsolatedFibreCurve
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
