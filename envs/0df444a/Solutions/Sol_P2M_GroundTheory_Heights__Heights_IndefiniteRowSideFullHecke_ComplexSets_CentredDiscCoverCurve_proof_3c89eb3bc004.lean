-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredDiscCoverCurve_proof_3c89eb3bc004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:13.330492+00:00
-- url     : https://prove2.me/submissions/8d447c63-da9b-4b81-8fc9-03e5fba73984

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCentredDiscCoverCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_punctured_branch_7f894f3acf71
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_extend_across_centre_fff121512849

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
open Topology Filter Metric Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CentredDiscCoverCurve
theorem _root_.solution (hPCC : PuncturedCoverCycles.Statement) :
    CentredDiscCoverCurve.Statement := by
  intro σ _ Y w p ρ N hY
  obtain ⟨δ, k, φ, hδ, hδ1, hk, hφd, hφi, hφY⟩ := centredDiscCover_punctured_branch hPCC hY
  exact centredDiscCover_extend_across_centre hY hδ hδ1 hk hφd hφi hφY
end CentredDiscCoverCurve
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
