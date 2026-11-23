-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.hform_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:24.685398+00:00
-- url     : https://prove2.me/submissions/82dd47bc-8dd8-4f49-a6ed-876de11fbf01

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
theorem _root_.solution (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J x y = ((s ∘ x) ᵥ* J) ⬝ᵥ y := by
  simp only [hform, vecMul, dotProduct, Finset.sum_mul, Function.comp]
  exact Finset.sum_comm
end PositivityTheory.PlacePermOperatorBicommutantSpan
