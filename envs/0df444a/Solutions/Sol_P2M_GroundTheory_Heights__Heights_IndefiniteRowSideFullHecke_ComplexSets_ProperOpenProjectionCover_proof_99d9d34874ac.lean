-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperOpenProjectionCover_proof_99d9d34874ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:00:03.779916+00:00
-- url     : https://prove2.me/submissions/5399ee27-fb7c-4ea2-976c-7411c412ae0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionBranchLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperOpenProjectionCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_subset_closure_nonvanishing_of_open_d99eecfc5c98

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
namespace ProperOpenProjectionCover
theorem _root_.solution (hbranch : ProperOpenProjectionBranchLocus.Statement)
    (hcount : UnbranchedProperCountConstant.Statement) : ProperOpenProjectionCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨δ, hδ, hne, hsec⟩ := hbranch σ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨N, hN⟩ := hcount σ (X ∩ B) d A D δ hD hDc hmaps hprop hδ (fun x hx hx0 => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hsec x hx hx0
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hXV⟩)
  exact ⟨δ, N, hδ, hne, hN, hsec, subset_closure_nonvanishing_of_open hDc hmaps hopen hδ hne⟩
end ProperOpenProjectionCover
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
