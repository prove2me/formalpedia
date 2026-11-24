-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:49.321798+00:00
-- url     : https://prove2.me/submissions/1a596bde-c617-404e-a73d-148716c97fa4

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_blk_map
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_hypJ_eq

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
theorem _root_.solution {L : Type} [CommRing L] (φ : K →+* L) (J : Matrix (Fin M) (Fin M) K) :
    (hypJ J).map φ = hypJ (J.map φ) := by
  simp only [hypJ_eq, blk_map, map_zero, map_one]
  congr 1 <;> exact funext fun _ => map_zero φ
end PositivityTheory.PlacePermOperatorBicommutantSpan
