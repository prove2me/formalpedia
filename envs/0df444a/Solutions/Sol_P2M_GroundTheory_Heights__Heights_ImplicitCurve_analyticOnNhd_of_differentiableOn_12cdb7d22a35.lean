-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ImplicitCurve_analyticOnNhd_of_differentiableOn_12cdb7d22a35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:19.338437+00:00
-- url     : https://prove2.me/submissions/7a47d097-494d-4c8c-a9a0-7e71934c54af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StImplicitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImplicitCurve
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Topology Metric
noncomputable section
open GroundTheory.Heights₂.Heights.ImplicitCurve
namespace GroundTheory.Heights₂.Heights.ImplicitCurve
theorem _root_.solution {m p : ℕ} {U : Set (Fin m → ℂ)}
    {Φ : (Fin m → ℂ) → Fin p → ℂ} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticOnNhd ℂ Φ U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => Φ t j) U := differentiableOn_pi.1 hΦ j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => Φ t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]; exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt
end GroundTheory.Heights₂.Heights.ImplicitCurve
