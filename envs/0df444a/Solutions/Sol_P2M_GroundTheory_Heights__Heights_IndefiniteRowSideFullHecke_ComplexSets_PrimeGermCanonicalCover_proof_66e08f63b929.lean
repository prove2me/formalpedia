-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermCanonicalCover_proof_66e08f63b929
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:35.731779+00:00
-- url     : https://prove2.me/submissions/018b04f6-b935-4b37-871c-e4db4f2ddf78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermCanonicalCover

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimeGermCanonicalCover
theorem _root_.solution (h₁ : PrimeGermPrimitivePresentation.Statement)
    (h₂ : PrimitivePresentationCover.Statement) : PrimeGermCanonicalCover.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, ℓ, N, c, δ, hpres, hδ⟩ := h₁ σ w k p hp hP
  have hδa : AnalyticAt ℂ δ (A w) := hpres.2.1
  have hdiv := hpres.2.2.2.2.2.1
  refine ⟨d, A, ℓ, N, δ, hδa, hδ, ?_, h₂ σ w k p d A ℓ N c δ hp hpres⟩
  intro g hg
  obtain ⟨M, a, ha, h, hh, hev⟩ := hdiv g hg
  exact ⟨M, a, h, ha, hh, hev⟩
end PrimeGermCanonicalCover
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
