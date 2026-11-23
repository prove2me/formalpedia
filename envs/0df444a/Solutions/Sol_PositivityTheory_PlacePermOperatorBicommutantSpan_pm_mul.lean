-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.pm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:54.452672+00:00
-- url     : https://prove2.me/submissions/02a2a81d-6395-42e9-bffd-022547cea6e3

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_blk_mul

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
theorem _root_.solution (a b d a' b' d' : K) (r w r' w' : Fin M → K) (U U' : Matrix (Fin M) (Fin M) K) :
    pm a b r d w U * pm a' b' r' d' w' U' =
      pm (a * a') (a * b' + b * d' + r ⬝ᵥ w') (a • r' + r ᵥ* U') (d * d') (d' • w + U *ᵥ w') (U * U') := by
  simp [pm, blk_mul]
end PositivityTheory.PlacePermOperatorBicommutantSpan
