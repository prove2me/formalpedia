-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredNonemptyExecution.ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T04:53:30.87046+00:00
-- url     : https://prove2.me/submissions/ef285988-1314-48cd-84fb-c4d3b4c5af54

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinishCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationFields
import Definitions.Def_Submission_Weighted_Global_TernaryColoredInitializationResources
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredNonemptyExecution
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Definitions.Def_WeightedCache3SUM_Alias_96784e4910534891
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Definitions.Def_WeightedCache3SUM_Alias_f93cfd5252bad152
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedGlobalColoredInitializationProof_ends_then
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_ThreeSum_ReportingHostLevelData_Bounds_mono
import Theorems.Thm_ThreeSum_SourceBucketView_bounds
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocation_Allocation_constants
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_cells
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFinalBounds_words
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPostMemory_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Uniform_mono
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepare_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_next
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedDataReads_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedScoreReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalColoredConcreteFinalCall_call
import Theorems.Thm_ThreeSum_WeightedGlobalColoredFinalReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalColoredFinishCall_finish
import Theorems.Thm_ThreeSum_WeightedGlobalColoredInitializationResources_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopCall_call
import Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_ready
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationFields_header_before
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationFields_reads
import Theorems.Thm_ThreeSum_WeightedGlobalColoredProgramIdentity_color_eq
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredNonemptyExecution
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout WeightedGlobalLocalParameters
open LightWeightedGlobalColoredSolver LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredNonemptyExecution
theorem _root_.solution {lim : Limits} {d : ℕ} (P : Profile κ) (n free menu c : ℕ)
    (A B C oldA oldB oldC : List ℤ) (initial : ℕ→ℤ) (locals : List ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    (hcutoff : P.cutoff≤n) (hneed : (P.colorNeed n (n^κ)).Ok lim free d)
    (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (NA : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.av free n) n oldA A)
    (NB : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.bv free n) n oldB B)
    (NC : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.cv free n) n oldC C)
    (hheader : Seg initial (LightWeightedGlobalColorPreparation.headerAt free n (LightColorParametersCosts.width n))
      (LightWeightedGlobalColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C))
    (hOriginals : WeightedGlobalArenaPrefixInputs.Originals (input P n free A B C) (arrays P n free menu A B C)
      (q P n*q P n) P.radix P.radix n
      (WeightedGlobalComputedExtensionMenu.functional (p:=P.p) (c:=c) (dim_pos P n))
      (WeightedGlobalArenaFamilyBudget.seedAt (WeightedGlobalComputedExtensionMenu.seeds (p:=P.p) (d:=dim P n) (c:=c)))
      (WeightedGlobalArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (WeightedGlobalArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))
      (WeightedGlobalArenaSelectedSigned.requester (n^κ) P.radix (J P n) (fun i=>A.getD i 0)) initial)
    (h1 : frame locals 1=(n:ℤ))
    (h5 : frame locals 5=(LightWeightedGlobalColorPreparation.headerAt free n (LightColorParametersCosts.width n):ℤ)) :
    let S:=setup P n free menu c A B C initial
    Ends lim P.color d (initChunk P.p (4^fixedLength P.m) P.F (tail P)) ⟨frame locals,initial⟩
      (LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+
        S.initTime+postTime P n free menu c A B C initial+8000)
      (fun σ=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
          C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧
        Kept initial σ.mem (input P n free A B C).free) := by
  let S:=setup P n free menu c A B C initial
  let header:=LightWeightedGlobalColorPreparation.headerAt free n (LightColorParametersCosts.width n)
  let fn:=WeightedGlobalColoredPreparationFields.field P n free menu A B C
  let PT:=postTime P n free menu c A B C initial
  let Q:=fun σ : State=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
      C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧ Kept initial σ.mem S.input.free
  have Bnd:=WeightedGlobalColoredInitializationResources.bounds P n free A B C hneed hmeta
  have hinputs:=P.inputGuards n hcutoff
  have HR:=ready (depth:=d+2) P n free menu c A B C initial Bnd.hardware hmeta hinputs hOriginals
  have hEnd:=WeightedGlobalColoredPreparationFields.header_before P n free A B C
  change header+19≤(input P n free A B C).free at hEnd
  have hspace : (input P n free A B C).free≤lim.space := by have:=Bnd.hardware.cells;omega
  have hread:=WeightedGlobalColoredPreparationFields.reads hheader
  have next : ∀σ, Initialized P.allocation.D P.allocation.E P.K P.radix (P.p^(2*P.K)) P.drift P.scale
      n (n^κ) S.input.free (q P n) (J P n) (A.length*2^(J P n))
      (WeightedGlobalColoredLoopCall.initValues P n free menu A B C) (frame locals) σ.loc initial σ.mem →
      Ends lim P.color d (tail P) σ (S.initTime+PT+2000) Q := by
    intro σ HI
    have hloc5 : σ.loc 5=(header:ℤ) := HI.header.trans h5
    have hR : σ.mem (header+15)=(rounds P n:ℤ) :=
      (HI.kept _ (by change header+15<(input P n free A B C).free;omega)).trans (hread 15 (by decide))
    have hJ : σ.mem (header+16)=(J P n:ℤ) :=
      (HI.kept _ (by change header+16<(input P n free A B C).free;omega)).trans (hread 16 (by decide))
    have hc:=WeightedGlobalColoredLoopCall.call (d:=d) P n free menu c A B C initial (frame locals) σ.loc σ.mem
      HI HR hloc5 hR hJ (by omega)
    unfold tail
    apply Ends.pieceThen hc (hT:=by change 25+S.initTime≤S.initTime+PT+2000;omega)
    intro ω hw
    rcases hw with ⟨h12,hInv,hkeep⟩
    have hf:=WeightedGlobalColoredFinishCall.finish (d:=d) P n free menu c A B C oldA oldB oldC initial ω.mem ω.loc
      NA NB NC hmeta hcutoff (Bnd.hardware.mono le_rfl le_rfl (by omega)) hInv hheader hEnd
      ((hkeep 5 (by decide)).trans hloc5) ((hkeep 6 (by decide)).trans HI.arena)
      ((hkeep 7 (by decide)).trans HI.capacity) ((hkeep 10 (by decide)).trans HI.liveHost) h12
    exact hf.mono (by change 1000+PT≤S.initTime+PT+2000-(25+S.initTime);omega) (fun _ h=>h)
  have hi:=LightWeightedGlobalColoredInitializationProof.ends_then
    (radix:=P.radix) (D:=P.allocation.D) (E:=P.allocation.E) (K:=P.K) (bDigit:=P.radix)
    (a:=P.p^(2*P.K)) (b:=P.drift) (scaleBase:=P.scale) (p:=P.p) (R:=4^fixedLength P.m) (F:=P.F)
    S.raws S.words S.mapCodes
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    (WeightedGlobalColoredProgramIdentity.suffix P) locals initial fn h1 h5 hread hEnd
    (by have:=hinputs.1;omega) P.radix_gt_one.le hneed.space Bnd.finish Bnd.inputWord Bnd.exponentWord
    Bnd.menu Bnd.constants Bnd.budgetWord Bnd.depthBound (tail P) Q
    (fun σ h=>by
      change Ends lim (WeightedGlobalColoredProgramIdentity.libraries P++WeightedGlobalColoredProgramIdentity.suffix P)
        d (tail P) σ (S.initTime+PT+2000) Q
      rw [←WeightedGlobalColoredProgramIdentity.color_eq]
      exact next σ h)
  change Ends lim (WeightedGlobalColoredProgramIdentity.libraries P++WeightedGlobalColoredProgramIdentity.suffix P) _ _ _ _ _ at hi
  rw [←WeightedGlobalColoredProgramIdentity.color_eq] at hi
  exact hi.mono (by
    change LightWeightedGlobalColoredInitializationProof.time P.allocation.E P.K+(S.initTime+PT+2000)≤
      LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+S.initTime+PT+8000
    unfold LightWeightedGlobalColoredInitializationProof.time
    omega) (fun _ h=>h)
end ThreeSum.WeightedGlobalColoredNonemptyExecution
