-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaMomentResources.resources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:58:15.403805+00:00
-- url     : https://prove2.me/submissions/2fb6f842-f313-42ca-8e5f-f63871bcee86

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_WeightedGlobalArenaMomentResources_source_homogeneous
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_region_space
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_pairMass_le
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_rank
import Theorems.Thm_ThreeSum_WeightedGlobalArenaReporterBounds_channel_words
import Theorems.Thm_ThreeSum_WeightedGlobalMomentChannelResources_score_abs_le
import Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_score_abs_le
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaMomentResources
theorem _root_.solution {lim : Limits} {d originalB originalC M n U H : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (μ : ℕ→ℤ) (B C : ℕ→ℤ)
    (hM : 1<M) (hr : r≤Nat.clog M (n^2)) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hseed : ∀ k<2*H+1, ∀ j≤k,
      WeightedSourceCountExecutionFactory.Seed (setup (r := r) maps τ cap Q I) lim (d+2)
        (addr I.free I.capacity 28) μ
        (LightWeightedGlobalMomentChannelFactory.leftWeights k j B)
        (LightWeightedGlobalMomentChannelFactory.rightWeights k j C))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+2<lim.depth)
    (hend : finish I.free I.capacity≤lim.space)
    (hnBl : I.nB≤I.capacity) (hnCl : I.nC≤I.capacity)
    (hcount : (2*H+1)*(entries (r := r) maps τ I).length≤I.capacity)
    (hrecords : 3*(entries (r := r) maps τ I).length≤I.capacity)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 25)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 25)
    (hBspace : originalB+I.nB≤addr I.free I.capacity 25)
    (hCspace : originalC+I.nC≤addr I.free I.capacity 25)
    (hB : ∀ i<I.nB, μ (originalB+i)=B i)
    (hC : ∀ i<I.nC, μ (originalC+i)=C i)
    (hBabs : ∀ i<I.nB, |B i|≤(U : ℤ)) (hCabs : ∀ i<I.nC, |C i|≤(U : ℤ))
    (hchannelWord : ((channelNeed maps cap M H n U).word : ℤ)≤lim.word)
    (hargs : ∀ z∈LightWeightedGlobalMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
      originalB originalC (addr I.free I.capacity 25), |z|≤lim.word) :
    LightWeightedGlobalCertifiedMomentDriver.Resources (setup (r := r) maps τ cap Q I) lim d
      originalB originalC (addr I.free I.capacity 25) (2*H+1)
      (r*alphaRank m) (r*alphaRank m) U
      (WeightedGlobalMomentChannelResources.scoreBound (envelope maps cap M n) U (2*H)) μ B C := by
  have hpair := pairMass_le maps τ cap Q I M n hM hr hnB hnC
  have hwords := WeightedGlobalArenaReporterBounds.channel_words lim (envelope maps cap M n) U (2*H) hchannelWord
  have hc : (entries (r := r) maps τ I).length≤I.capacity := by nlinarith only [hcount]
  refine {
    hseed:=hseed
    himmutable:=?_
    hw:=hw
    hd:=hd
    hBspace:=hBspace
    hCspace:=hCspace
    hwindow:=before (by decide) hcount
    hleft:=before (by decide) hnBl
    hright:=region_space (by decide) hnCl hend
    houtBefore:=before (len := 0) (by decide) (by omega)
    hout:=region_space (by decide) hc hend
    hleftSpace:=region_space (len := 0) (by decide) (by omega) hend
    hB:=hB
    hC:=hC
    hBabs:=hBabs
    hCabs:=hCabs
    hscore:=?_
    hleftWord:=hwords.1
    hrightWord:=hwords.2.1
    haddWord:=hwords.2.2.1
    htermsWord:=hwords.2.2.2
    hargsWord:=hargs
    hleftHom:=source_homogeneous maps cap I false
    hrightHom:=source_homogeneous maps cap I true
    hQ:=?_ }
  · exact {
      leftInput:=before (by decide) hnBl
      leftCodes:=hbank
      leftPowers:=hpowers
      rightInput:=before (by decide) hnCl
      rightCodes:=hbank
      rightPowers:=hpowers
      frontCodes:=hbank
      frontRecords:=before (by decide) hrecords }
  · intro k hk j hj i hi
    exact WeightedGlobalMomentChannelResources.score_abs_le _ B C hpair hBabs hCabs (by omega) hj i
  · intro i hi
    exact WeightedGlobalArenaQueryModel.setup_rank hi
end ThreeSum.WeightedGlobalArenaMomentResources
