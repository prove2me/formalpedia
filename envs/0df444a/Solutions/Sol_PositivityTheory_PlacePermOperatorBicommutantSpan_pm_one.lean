-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.pm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:55.116371+00:00
-- url     : https://prove2.me/submissions/d6175bc4-1e57-4e9a-b935-48e71c5ab105

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
theorem _root_.solution : pm (1 : K) 0 (0 : Fin M → K) 1 0 1 = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [pm, blk, Matrix.one_apply, Fin.ext_iff]
end PositivityTheory.PlacePermOperatorBicommutantSpan
