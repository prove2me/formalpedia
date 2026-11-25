-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_proof_b970c246b777
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:21.809484+00:00
-- url     : https://prove2.me/submissions/f4f3145b-518f-40da-ae57-d225a5e6ceac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCircleArgumentPrinciple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_integral_prod_mul_c8dc6c3455c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_factorisation_d6b44edf3bc2

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
open Topology Filter Metric Complex Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CircleArgumentPrinciple
theorem _root_.solution : CircleArgumentPrinciple.Statement := by
  intro h O c r hr hO hball hh hsph
  obtain ⟨Z, u, hZ, hu, hu0, hfac⟩ := CircleArgumentPrinciple.factorisation hr hO hball hh hsph
  refine ⟨Z, u, hZ, hu, hu0, hfac, fun φ hφ => ?_⟩
  rw [← CircleArgumentPrinciple.integral_prod_mul hr hO hball hu hu0 hφ Z hZ]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro s hs
  have hsO : s ∈ O := hball (sphere_subset_closedBall hs)
  have heq : h =ᶠ[𝓝 s] fun w => (Z.map fun a => w - a).prod * u w :=
    Filter.eventually_of_mem (hO.mem_nhds hsO) hfac
  simp only [heq.deriv_eq, hfac s hsO]
end CircleArgumentPrinciple
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
