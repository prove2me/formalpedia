-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport.span_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:12:48.552953+00:00
-- url     : https://prove2.me/submissions/36c2ae98-293d-4e0a-963c-a7842c86044d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaGuardTransport
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaGuardTransport_guard
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_SourceBucketView_read
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCandidateGuard_guard
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_region_space
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceControls_controls
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_controls
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row


namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
private theorem coefficient_word_le (J p b power : ℕ) :
    LightPrimeCoefficient.word p≤LightTernaryAppendKeys.word (J+2) p b power := by
  have hm : (p+1)*(p+1)≤(p+1)*(p+b+1) := Nat.mul_le_mul_left _ (by omega)
  have hn : (p+1)*(p+b+1)≤(J+3)*((p+1)*(p+b+1)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hp := hm.trans hn
  unfold LightPrimeCoefficient.word LightTernaryAppendKeys.word LightSignedRowHash.word
  nlinarith
end ThreeSum.WeightedGlobalArenaGuardTransport
end
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport
theorem _root_.solution {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : WeightedGlobalArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : WeightedGlobalArenaCandidateGuard.Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (h : KeepInputs I μ ν) (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hτ : 0<τ) (hraw : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(WeightedGlobalArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).score K|≤lim.word)
    (hnewSpan : A.J*p^(r-1)*p≤I.capacity) :
    LightWeightedGlobalControllerFactory.SpanGuard (config p r I A seed) D lim depth
      (addr I.free I.capacity 8) ν := by
  have H := guard maps τ cap Q I A D μ ν L R M G B h hprefix hτ hraw hpaired
  have ha := H.1.append
  have hs := H.1.span
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hsource : A.J*p^(r-1)≤I.capacity :=
    (Nat.le_mul_of_pos_right _ hp).trans hnewSpan
  have rowBefore : (config p r I A seed).row+A.J≤addr I.free I.capacity 8 := by
    have hm := M.menu
    have hfree : I.free≤addr I.free I.capacity 8 := by unfold addr; omega
    omega
  refine {
    represents:=hs.represents
    rowsPos:=by change 0<p^(r-1); positivity
    spaceWord:=G.wordSpace
    source:=before (by decide) hsource
    row:=rowBefore
    output:=region_space (by decide) hnewSpan G.capacity.endSpace
    word:=(Int.ofNat_le.mpr (coefficient_word_le A.J p D.bB (p^(r-1)))).trans ha.Bword
    controls:=hs.controls
    bounded:=hs.bounded
    read:=hs.read
    rowRead:=?_
    depth:=by have := ha.depth; omega }
  intro i hi
  have hd : D.coeff i=LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i := hs.digits i hi
  rw [←hd]
  exact ha.coeffRead i (by change i<A.J+2; change i<A.J at hi; omega)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport
