-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_analyticOnNhd_of_differentiableOn_pi_eff0fba7ce93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:26.766981+00:00
-- url     : https://prove2.me/submissions/b2e7b575-e1cd-4dcc-afca-cf3b7a86048a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaximalCountUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaximalCountUnbranched
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
open Topology Filter Metric
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
theorem _root_.solution {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U := differentiableOn_pi.1 hG s
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched
