-- Prove2me | solution 1 for ThreeSum.LightBlockSourcePreparation.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:31:19.674113+00:00
-- url     : https://prove2.me/submissions/b48327a6-f943-4012-9055-cba549c1174f

import Definitions.Def_Submission_ThreeSum_LightSourcePreparation
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
import Definitions.Def_Submission_ThreeSum_LightBlockSourcePreparation
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_left
import Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_right
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_le
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_lt
import Theorems.Thm_ThreeSum_BlockSourceFlags_candidateIndices_lt
import Theorems.Thm_ThreeSum_BlockSourceFlags_left_product
import Theorems.Thm_ThreeSum_BlockSourceFlags_right_product
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_f318d8b49c9fc733
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_bff01fd4b2900a53
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Definitions.Def_WeightedCache3SUM_Alias_a076d5b93ecac4d9
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourcePreparation
open Light BlockRows BlockIndex BlockEncoding BlockCoefficientRows BlockSourceFlags
open LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1700000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourcePreparation
theorem _root_.solution {pMain : ℕ} (C : LightSourcePreparation.Procs P pMain)
    {μ : ℕ → ℤ} {h J occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags
      bitBase rowOut work : ℕ}
    (o : Occurrences h J) (sets : ℕ → Finset (Coord J (512*h)))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+5 ≤ lim.depth)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*(512*h)*scheduleSize h ≤ coeff0)
    (hcandidates : candidates+scheduleSize h ≤ coeff0)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ coeff0)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(512*h) ≤ coeff1)
    (hc1 : coeff1+J*(512*h) ≤ rawLeft) (hrawLeft : rawLeft+n ≤ rawRight)
    (hrawRight : rawRight+n ≤ flags) (hflags : flags+2*n+2 ≤ bitBase)
    (hbits : bitBase+J*(512*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : LightSourcePreparation.space work J (512*h) (localPrime h) ≤ lim.space)
    (hword : (LightSourcePreparation.word J (512*h) (localPrime h) (localPrime h)
      ((512*h).choose h) (localBucketCap h) : ℤ) ≤ lim.word)
    (hoccRead : ∀ j < J, μ (occ+j) = (occurrenceIndices o j : ℤ))
    (hcandidateRead : ∀ s : Occurrence h,
      μ (candidates+s.val) = (LightLocalCoverSchedule.candidateAt h s : ℤ))
    (hread0 : ∀ s < scheduleSize h, ∀ a < 512*h,
      μ (maps+2*(512*h)*s+a) = (mapRow h false s a : ℤ))
    (hread1 : ∀ s < scheduleSize h, ∀ a < 512*h,
      μ (maps+2*(512*h)*s+512*h+a) = (mapRow h true s a : ℤ))
    (hcountL : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      μ (histL+k*localPrime h+r) = (leftCount h k r : ℤ))
    (hcountR : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      μ (histR+k*localPrime h+r) = (rightCount h k r : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (SubsetAddress.subsetMask (indexSet (sets i)) : ℤ)) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,occ,maps,candidates,histL,histR,masks,n,
        coeff0,coeff1,rawLeft,rawRight,flags,bitBase,rowOut,work]
      μ (LightSourcePreparation.time n J (512*h) (localPrime h)) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = endpointRight o (sets i)) ∧
        (∀ i < n, ν (flags+i) = (if LeftAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        (∀ i < n, ν (flags+n+i) = (if RightAllowed o (sets i) then 1 else 0 : ℕ)) ∧
        Kept μ ν coeff0) := by
  have hcandidates' : ∀ s < scheduleSize h, μ (candidates+s) = (candidateIndices h s : ℤ) := by
    intro s hs
    exact hcandidateRead ⟨s,hs⟩
  have hboundL : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      leftCount h k r ≤ (512*h).choose h := by
    intro k hk r hr
    exact LightHistogram.count_le _ _ _
  have hboundR : ∀ k < LightLocalCoverSchedule.rows h, ∀ r < localPrime h,
      rightCount h k r ≤ (512*h).choose h := by
    intro k hk r hr
    exact LightHistogram.count_le _ _ _
  have run := C.meets (d := d) (μ := μ) (J := J) (L := 512*h) (h := h)
    (p := localPrime h) (cap := localBucketCap h) (occ := occ) (maps := maps)
    (candidates := candidates) (histL := histL) (histR := histR) (masks := masks) (n := n)
    (coeff0 := coeff0) (coeff1 := coeff1) (rawLeft := rawLeft) (rawRight := rawRight)
    (flags := flags) (bitBase := bitBase) (rowOut := rowOut) (work := work)
    (U := localPrime h) (V := (512*h).choose h) (M := scheduleSize h)
    (K := LightLocalCoverSchedule.rows h)
    (occurrenceIndices o) (candidateIndices h) (fun i => SubsetAddress.subsetMask (indexSet (sets i)))
    (mapRow h false) (mapRow h true) (leftCount h) (rightCount h)
    hw hd (localPrime_pos h) (by omega) hocc hmaps hcandidates hleft hright hmasks hc0 hc1 hrawLeft
    hrawRight hflags hbits hrowOut hspace hword (fun _ hj => occurrenceIndices_lt o hj)
    (fun _ hs => candidateIndices_lt hs) hoccRead hcandidates' hread0 hread1
    (fun _ hs _ ha => mapRow_le false hs ha) (fun _ hs _ ha => mapRow_le true hs ha)
    hcountL hcountR hboundL hboundR hmaskRead
    (fun i _ => (SubsetAddress.subsetMask_isMask (indexSet (sets i))).1)
  refine run.mono le_rfl ?_
  rintro r ν ⟨rawL,rawR,left,right,kept⟩
  exact ⟨fun i hi => (rawL i hi).trans (eval_left o (sets i)),
    fun i hi => (rawR i hi).trans (eval_right o (sets i)),
    fun i hi => (left i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (left_product o (sets i))),
    fun i hi => (right i hi).trans (congrArg (fun n : ℕ => (n : ℤ)) (right_product o (sets i))),kept⟩
end ThreeSum.LightBlockSourcePreparation
