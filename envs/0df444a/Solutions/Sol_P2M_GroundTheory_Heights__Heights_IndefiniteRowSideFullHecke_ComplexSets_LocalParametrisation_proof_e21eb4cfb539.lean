-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalParametrisation_proof_e21eb4cfb539
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:22.144804+00:00
-- url     : https://prove2.me/submissions/4bf05128-b0c0-41a4-bc5a-d3f6f243ce10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalParametrisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalParametrisation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_proper_projection_nbhd_b097f0104f75

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
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace LocalParametrisation
theorem _root_.solution (hproj : GermFiniteProjection.Statement)
    (hcov : FiniteGermProjectionCover.Statement) : LocalParametrisation.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, hiso, hinj⟩ := hproj σ X w hX hirr
  obtain ⟨N₀, hN₀, hcovB⟩ := hcov σ X w d A hX hirr hiso hinj
  obtain ⟨B, D, hBo, hBU, hwB, hDo, hDc, hmaps, hprop, hisoB⟩ :=
    exists_proper_projection_nbhd A hX hirr.1 hiso (Filter.inter_mem hU hN₀)
  obtain ⟨δ, N, hP⟩ :=
    hcovB B D hBo (hBU.trans Set.inter_subset_right) hwB hDo hDc hmaps hprop hisoB
  exact ⟨d, A, B, D, δ, N, hBU.trans Set.inter_subset_left, hP⟩
end LocalParametrisation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
