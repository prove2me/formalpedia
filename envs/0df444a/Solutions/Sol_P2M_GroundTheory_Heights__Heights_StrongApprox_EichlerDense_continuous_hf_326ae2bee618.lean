-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_hf_326ae2bee618
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:51.329103+00:00
-- url     : https://prove2.me/submissions/cb73f248-8684-4993-b2d3-1bede63d7e92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) {x y : X → Fin N → S}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => hf σ J (x t) (y t) := by
  unfold hf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_apply i).comp hx).mul continuous_const).mul
    (hσ.comp ((continuous_apply j).comp hy))
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
