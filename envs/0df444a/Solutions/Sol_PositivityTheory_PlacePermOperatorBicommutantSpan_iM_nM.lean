-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.iM_nM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:49.646256+00:00
-- url     : https://prove2.me/submissions/a6962829-0028-49fb-b3b4-a32cf83b3064

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
theorem _root_.solution {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) (w : Fin M → K) (z : K) :
    pm 1 0 0 1 0 U * nM s J w z = nM s J (U *ᵥ w) z * pm 1 0 0 1 0 U := by
  have e : (s : K → K) ∘ (U *ᵥ w) = (s ∘ w) ᵥ* cT s U := by
    funext i; simp [vecMul, mulVec, dotProduct, cT, mul_comm]
  simp [nM, pm_mul, e, neg_vecMul, hU]
end PositivityTheory.PlacePermOperatorBicommutantSpan
