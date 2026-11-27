-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RegularLocusIdentity_proof_9ed1c77c2ad9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:26.622949+00:00
-- url     : https://prove2.me/submissions/716016ed-5f8a-4ab7-b22a-3a2bcf6cc3b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsRegularPointOf_exists_ball_chart_9fbbc9253110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_on_chart_of_eventually_eq_zero_fd49f49455cd

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
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RegularLocusIdentity
theorem _root_.solution (hreg : RegularOffHypersurface.Statement) :
    RegularLocusIdentity.Statement := by
  intro σ _ I hI
  obtain ⟨h, hhI, hh⟩ := hreg σ I hI
  refine ⟨h, hhI, fun z hz hhz W hW => ?_⟩
  obtain ⟨d, V, B, g, hVo, hzV, hVW, hBo, hBc, hg, hYV⟩ := (hh z hz hhz).exists_ball_chart hW
  exact ⟨V, hVo, hzV, hVW, fun F hF h0 => eq_zero_on_chart_of_eventually_eq_zero hBo hBc hg hYV F hF h0⟩
end RegularLocusIdentity
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
