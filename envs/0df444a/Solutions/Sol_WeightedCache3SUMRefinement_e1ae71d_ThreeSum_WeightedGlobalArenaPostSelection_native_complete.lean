-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostSelection.native_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:13:56.25635+00:00
-- url     : https://prove2.me/submissions/2ae025a4-907a-4979-bae7-7774def9a7a9

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCompactSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaMomentResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPostSelection
import Theorems.Thm_ThreeSum_TernaryMomentMatrixInvariant_complete
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaNativeComplete_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaReporterBounds_compact_abs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCompleteFrontend_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostSelection
open Light LightOriginalSurvivors LightWeightedGlobalPostSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps TernarySignedReduction
open TernaryExtensionEncoding WeightedGlobalArenaLayout
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r J : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostSelection
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hcover : ∀a b : ZMod p, ∃i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<I.nB, |B j|≤(U : ℤ))
    (hC : ∀k<I.nC, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    let I' := selectedInput I U radix nA H A B C keysB keysC
    let S := setup (r := r) maps τ cap Q I'
    (∃i<S.front.count, ∃pair : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mode (compact keysB B I.nB) (compact keysC C I.nC) pair=
        A (WeightedGlobalArenaNativeComplete.originalPosition (r := r) maps τ I' i)) ↔
      ∃i<nA, ∃j<(indices keysB I.nB).length, ∃k<(indices keysC I.nC).length,
        compact keysC C I.nC k=A i+compact keysB B I.nB j := by
  exact WeightedGlobalArenaNativeComplete.complete maps τ cap Q (compactInput I keysB keysC)
    U radix nA H A (compact keysB B I.nB) (compact keysC C I.nC) hcover hA
    (WeightedGlobalArenaReporterBounds.compact_abs keysB B I.nB U hB)
    (WeightedGlobalArenaReporterBounds.compact_abs keysC C I.nC U hC) hcap
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPostSelection
