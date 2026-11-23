-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:43.8478+00:00
-- url     : https://prove2.me/submissions/a0d726dc-c67a-4267-9c7b-90cf3a714934

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (J : Matrix (Fin M) (Fin M) K) : hypJ J = blk 0 1 0 1 0 0 0 0 J := rfl
end PositivityTheory.PlacePermOperatorBicommutantSpan
