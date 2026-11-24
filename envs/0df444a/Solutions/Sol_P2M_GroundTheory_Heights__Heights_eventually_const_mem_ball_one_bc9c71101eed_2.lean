-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_eventually_const_mem_ball_one_bc9c71101eed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:58.013807+00:00
-- url     : https://prove2.me/submissions/3f4a21be-bee0-4df4-9510-51bd19ca8f43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrdersLiftCentre

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
open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have hc : Continuous (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) := continuous_pi fun _ ↦ continuous_id
  exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)
end GroundTheory.Heights₂.Heights
