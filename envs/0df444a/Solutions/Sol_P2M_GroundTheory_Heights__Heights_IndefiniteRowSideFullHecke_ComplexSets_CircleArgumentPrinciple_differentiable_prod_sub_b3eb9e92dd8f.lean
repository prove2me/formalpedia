-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_differentiable_prod_sub_b3eb9e92dd8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:55.845904+00:00
-- url     : https://prove2.me/submissions/2f4c13a5-3e3c-401f-bf20-ef4ab560e8eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCircleArgumentPrinciple

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
theorem _root_.solution (Z : Multiset ℂ) :
    Differentiable ℂ fun s : ℂ => (Z.map fun a => s - a).prod := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_id.sub_const a).mul ih
end CircleArgumentPrinciple
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
