-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaNativeComplete.complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:50:39.461181+00:00
-- url     : https://prove2.me/submissions/f158265e-9265-4daf-bb66-15dea1873a5c

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaNativeComplete
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryModel_setup_address
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCertificate_sources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCompleteFrontend_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeRequesterCoverage_complete
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearCanonical_complete


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaNativeComplete
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernarySignedReduction
open WeightedGlobalArenaSourceSetup TernaryExtensionEncoding WeightedGlobalNativeRequesterCoverage
variable {p m F r J : ℕ} [Fact p.Prime]
set_option maxHeartbeats 4000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaNativeComplete
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (U radix nA : ℕ)
    (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (A B C : ℕ→ℤ)
    (hcover : ∀a b : ZMod p, ∃i, WeightedGlobalCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<I.nB, |B j|≤(U : ℤ))
    (hC : ∀k<I.nC, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    let I' := input I U radix nA H A B C
    let S := setup (r := r) maps τ cap Q I'
    (∃i<S.front.count, ∃pair : WeightedGlobalNativePairMoments.Pair S i,
      WeightedGlobalNativePairMoments.mode B C pair=A (originalPosition (r := r) maps τ I' i)) ↔
      ∃i<nA, ∃j<I.nB, ∃k<I.nC, C k=A i+B j := by
  let I' := input I U radix nA H A B C
  let S := setup (r := r) maps τ cap Q I'
  have hqueries : WeightedGlobalNativeCompleteFrontend.Queries S maps τ U radix H A nA
      (originalPosition (r := r) maps τ I') := by
    refine ⟨rfl,?_,?_,?_⟩
    · intro i hi; rfl
    · intro i hi; exact WeightedGlobalArenaQueryModel.setup_address hi
    · intro i hi; rfl
  exact WeightedGlobalNativeCompleteFrontend.complete S maps cap τ hcover H A B C
    (originalPosition (r := r) maps τ I')
    (WeightedGlobalArenaSourceCertificate.sources maps τ cap Q I') hqueries
    (by intros; rfl) (by intros; rfl) hA hB hC hcap
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaNativeComplete
