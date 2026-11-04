-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceCountSeed.seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:10:53.647493+00:00
-- url     : https://prove2.me/submissions/00d9fad4-8bd7-4445-96ad-fc6f4afde625

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSeed
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_bank_size
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_ready
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceCountSeed
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaSourceCountSeed
theorem _root_.solution {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
    (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := d+1) (r := r) maps τ cap I)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hprefix : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 28)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (G : ∀right, WeightedGlobalArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space)
    (W : ∀right, WeightedGlobalArenaSourceControls.Controls (r := r) maps cap I right lim (d+1))
    (M : Reads (r := r) maps τ I μ)
    (hleft : ∀i<I.nB, |leftWeight i|≤(I.weightCap : ℤ))
    (hright : ∀i<I.nC, |rightWeight i|≤(I.weightCap : ℤ)) :
    WeightedSourceCountExecutionFactory.Seed (setup (r := r) maps τ cap localQ I) lim d
      (addr I.free I.capacity 28) μ leftWeight rightWeight := by
  have hnb := WeightedGlobalArenaCountReady.bank_size hN
  have hfour : 4^(N m r)=2^(2*N m r) := by rw [Nat.pow_mul]
  have hbank : I.prefixFree+nb m r≤addr I.free I.capacity 28 := by omega
  have h28_30 : addr I.free I.capacity 28≤addr I.free I.capacity 30 := before (by decide) (by omega : 0≤I.capacity)
  have hgroup : F^r*nb m r+1≤lim.space := by
    have hp := C.powers
    have hs := C.endSpace
    have hg := C.bankValues
    unfold finish addr slots at hs
    omega
  have mem (right : Bool) : WeightedGlobalArenaSourceSeed.Memory (r := r) maps cap I right lim μ
      (if right then rightWeight else leftWeight) := by
    refine {
      nonempty:=hlocal right
      sourceBefore:=?_
      weightsBefore:=?_
      bankBefore:=?_
      powersBefore:=?_
      groupSpace:=hgroup
      bankSize:=hnb
      input:=?_
      inputBound:=?_
      weights:=?_
      codes:=M.codes
      powers:=M.powers }
    · cases right
      · exact before (by decide) hnB
      · exact before (by decide) hnC
    · cases right
      · exact before (by decide) hnB
      · exact before (by decide) hnC
    · cases right
      · exact hbank.trans (before (by decide) (by omega : 0≤I.capacity))
      · exact hbank.trans (before (by decide) (by omega : 0≤I.capacity))
    · cases right
      · exact hprefix.trans (before (by decide) (by omega : 0≤I.capacity))
      · exact hprefix.trans (before (by decide) (by omega : 0≤I.capacity))
    · cases right
      · exact M.left
      · exact M.right
    · cases right
      · exact M.leftBound
      · exact M.rightBound
    · cases right
      · exact hleft
      · exact hright
  refine {
    layout:=?_
    left:=WeightedGlobalArenaSourceSeed.seed maps cap I false hF hw (G false) (W false) (mem false)
    right:=WeightedGlobalArenaSourceSeed.seed maps cap I true hF hw (G true) (W true) (mem true)
    front:=WeightedGlobalArenaCountReady.ready maps τ cap localQ I μ leftWeight rightWeight hF hN hw C M.codes M.wanted hleft hright
    leftInputBefore:=before (by decide) hnB
    leftCodesBefore:=hbank
    leftPowersBefore:=hprefix
    rightInputBefore:=before (by decide) hnC
    rightCodesBefore:=hbank
    rightPowersBefore:=hprefix
    frontCodesBefore:=hbank
    frontRecordsBefore:=before (by decide) C.records
    boundaryBefore:=h28_30
    depth:=by have := C.depth; omega }
  refine {
    leftBank:=rfl
    rightBank:=rfl
    leftGroups:=rfl
    rightGroups:=rfl
    leftValues:=rfl
    rightValues:=rfl
    leftBeforeRight:=before (by decide) (by omega : 0≤I.capacity)
    leftBeforeFront:=before (by decide) (by omega : 0≤I.capacity)
    leftValuesEnd:=before (by decide) C.bankValues
    rightInputBefore:=before (by decide) hnC
    rightWeightsBefore:=before (by decide) hnC
    rightCodesBefore:=hbank.trans h28_30
    rightPowersBefore:=hprefix.trans h28_30
    frontCodesBefore:=hbank.trans h28_30
    frontRecordsBefore:=before (by decide) C.records }
end ThreeSum.WeightedGlobalArenaSourceCountSeed
