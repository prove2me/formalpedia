-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.nim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:33.388805+00:00
-- url     : https://prove2.me/submissions/689bd83e-a576-415f-b003-a4b1ee72c1df

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_pm_mul

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
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (w : Fin M → K) (z a d : K) (U : Matrix (Fin M) (Fin M) K) :
    nM s J w z * pm 1 0 0 1 0 U * pm a 0 0 d 0 1 = pm a (z * d) (-(((s ∘ w) ᵥ* J) ᵥ* U)) d (d • w) U := by
  simp [nM, pm_mul, neg_vecMul]
end PositivityTheory.PlacePermOperatorBicommutantSpan
